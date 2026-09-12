import RequestProject.Spine.Solder.Solder

/-!
# Spine / Solder : the associated internal Lorentz vector bundle

**Fifth module of the Task-34 tangent/solder layer.**

The projected internal Lorentz cocycle of an emergent Spin seed is packaged here as a
genuine Mathlib `VectorBundleCore` over the emergent base `EmergentBase.Space B`, with model
fibre the four-dimensional local model and with transition functions *exactly* the projected
Lorentz action:

`SpinNative.internalLorentzBundleCore S`.

Two points of bookkeeping.

* **Orientation of the coordinate changes.**  Mathlib's `VectorBundleCore.coordChange i j x`
  converts `i`-coordinates into `j`-coordinates and composes as
  `coordChange j k ∘ coordChange i j = coordChange i k`, whereas the project's Čech
  convention is `g_ij · g_jk = g_ik` with `g_ij` converting `j`-coordinates into
  `i`-coordinates (`e_j = e_i ∘ g_ij`).  The two are matched by
  `coordChange i j x = ρ(g̃_ji)(x)`, which is the *only* choice making both laws hold; it is
  recorded in `SpinNative.internalLorentzBundleCore_coordChange`.
* **Regularity.**  Continuity of the coordinate changes in the operator-norm topology of
  `LocalModel →L[ℝ] LocalModel` is derived from the continuity of the Spin cocycle in the
  intrinsic topology of `GLor`, through the module-topology uniqueness of the
  finite-dimensional endomorphism algebra of the carrier (`SpinCore.EndLor`).

## What is deliberately *not* packaged (Task 34 §10)

An isomorphism of *topological vector bundles* `InternalLorentzBundle ≃ TangentBundle` is
**not** constructed, and this is not an oversight: the solder datum
`SpinNative.TangentSolderData` deliberately imposes no continuity on the frames themselves
(only the overlap law, whose regularity is automatic), so there is nothing from which the
continuity of such an isomorphism could be derived.  What *is* proved is the fibrewise
statement together with the exact intertwining of the two transition systems
(`SpinNative.TangentSolderData.toInternalLorentzFiberEquiv`,
`SpinNative.TangentSolderData.coordChange_intertwines`), which is the whole invariant content
of the commuting square.  The missing ingredient is recorded in `TASK34_AUDIT.md`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

/-! ## `GLor` acts by continuous linear automorphisms -/

/-- A member of the intrinsic Lorentz group of the carrier, as a continuous linear map of the
local model.  The local model is finite-dimensional, so this is not an extra hypothesis. -/
def glorToCLM (F : ↥GLor) : LocalModel →L[ℝ] LocalModel :=
  LinearMap.toContinuousLinearMap ((F : LocalModel ≃ₗ[ℝ] LocalModel) : LocalModel →ₗ[ℝ] LocalModel)

@[simp] theorem glorToCLM_apply (F : ↥GLor) (v : LocalModel) :
    glorToCLM F v = (F : LocalModel ≃ₗ[ℝ] LocalModel) v := rfl

/-- **DERIVED (Task 34).**  The action of `GLor` on the local model is continuous into the
operator topology: the intrinsic topology of `GLor` and the operator-norm topology of the
endomorphisms of the four-dimensional local model are compatible. -/
theorem continuous_glorToCLM : Continuous glorToCLM := by
  have h1 : Continuous fun F : ↥GLor => ((F : LocalModel ≃ₗ[ℝ] LocalModel) : EndLor) :=
    continuous_lorAut_toLinearMap.comp continuous_subtype_val
  have h2 : Continuous
      (LinearMap.toContinuousLinearMap : EndLor → (LocalModel →L[ℝ] LocalModel)) :=
    IsModuleTopology.continuous_of_linearMap
      (LinearMap.toContinuousLinearMap :
        EndLor ≃ₗ[ℝ] (LocalModel →L[ℝ] LocalModel)).toLinearMap
  exact h2.comp h1

/-! ## The associated bundle -/

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- The index of a piece of the emergent cover containing a given point. -/
def coverIndex (B : BaseGluingData LocalModel ι) (x : Space B) : ι :=
  ((emergentCover B).covers x).choose

theorem mem_coverIndex (x : Space B) : x ∈ (emergentCover B).U (coverIndex B x) :=
  ((emergentCover B).covers x).choose_spec

/-- **NEWLY DEFINED (Task 34), PRINCIPAL — the internal Lorentz bundle.**  The vector bundle
over the emergent manifold whose model fibre is the internal Lorentz model of the Clifford
core and whose transition functions are exactly the projected Spin/Lorentz cocycle of the
emergent Spin seed.  Nothing is chosen beyond the index-selection function forced by
Mathlib's `VectorBundleCore` interface. -/
def internalLorentzBundleCore (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    VectorBundleCore ℝ (Space B) LocalModel ι where
  baseSet i := (emergentCover B).U i
  isOpen_baseSet i := (emergentCover B).isOpen_U i
  indexAt := coverIndex B
  mem_baseSet_at x := mem_coverIndex x
  coordChange i j x := glorToCLM ((project internalSpinProjection S).g j i x)
  coordChange_self i x hx v := by
    have h := (project internalSpinProjection S).g_self i hx
    rw [glorToCLM_apply, h]
    rfl
  continuousOn_coordChange i j :=
    continuous_glorToCLM.comp_continuousOn
      (((project internalSpinProjection S).continuousOn_g j i).mono
        (fun x hx => ⟨hx.2, hx.1⟩))
  coordChange_comp i j k x hx v := by
    obtain ⟨⟨hi, hj⟩, hk⟩ := hx
    have h := (project internalSpinProjection S).cocycle k j i x ⟨⟨hk, hj⟩, hi⟩
    have := congrArg (fun g : ↥GLor => (g : LocalModel ≃ₗ[ℝ] LocalModel) v) h
    simpa using this

@[simp] theorem internalLorentzBundleCore_baseSet
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i : ι) :
    (internalLorentzBundleCore S).baseSet i = (emergentCover B).U i := rfl

/-- **DERIVED (Task 34).**  The transition functions of the internal Lorentz bundle *are*
the projected internal Lorentz transitions, in the inverse-index convention forced by
Mathlib's composition law for `VectorBundleCore`. -/
@[simp] theorem internalLorentzBundleCore_coordChange
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B)
    (v : LocalModel) :
    (internalLorentzBundleCore S).coordChange i j x v
      = projectedLorentzTransition S j i x v := rfl

/-! ## The solder datum as a fibrewise equivalence with the tangent bundle -/

namespace TangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)} (E : TangentSolderData B S)

/-- **NEWLY DEFINED (Task 34).**  The solder identification, read as an identification of
the fibre of the internal Lorentz bundle with the genuine tangent space. -/
def toInternalLorentzFiberEquiv (x : Space B) :
    (internalLorentzBundleCore S).Fiber x ≃ₗ[ℝ] TangentSpace localModelI x :=
  E.tangentLinearEquiv x

/-- **DERIVED (Task 34), PRINCIPAL — the intertwining property.**  Over a double overlap the
solder frames intertwine the coordinate changes of the internal Lorentz bundle with the
identity of the tangent fibre: the frame of the piece `j` composed with the bundle's
coordinate change from `j` to `i` is the frame of the piece `i`.

This is the commuting square of Task 34 §9 in bundle language; it is the exact invariant
content of the (topologically un-packaged) bundle isomorphism. -/
theorem coordChange_intertwines (i j : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).overlap₂ i j) (v : LocalModel) :
    E.frame i x ((internalLorentzBundleCore S).coordChange j i x v) = E.frame j x v := by
  rw [internalLorentzBundleCore_coordChange]
  exact (E.compatibility i j x hx v).symm

end TangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.internalLorentzBundleCore
#print axioms SpinNative.TangentSolderData.coordChange_intertwines
