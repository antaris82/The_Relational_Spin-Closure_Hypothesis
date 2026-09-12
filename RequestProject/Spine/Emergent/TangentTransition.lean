import RequestProject.Spine.Emergent.SmoothStructure

/-!
# Spine / Emergent : the genuine tangent transition data of the emergent smooth manifold

**First module of the Task-34 tangent/solder layer, and the *bottom* of it.**

Task 33 closed the smooth gate: a base-gluing datum `B : BaseGluingData LocalModel ι` whose
identification maps are smooth (`B.SmoothGluing`) makes the Task-32 reconstructed charted
space `EmergentBase.Space B` a `C^∞` manifold over the four-dimensional local model, for the
*existing* atlas.  Task 34 asks what the **tangent bundle** of that manifold actually is, and
whether it is coupled to the internal Lorentz structure of the Clifford/Spin core.

This module answers the first half of that question, and *only* the first half:

* `EmergentBase.BaseGluingData.tangentTransitionMap B i j y` — the candidate tangent
  coordinate transition: the derivative `D(φ_ij)(y)` of the primitive identification map on
  its incidence domain;
* `EmergentBase.BaseGluingData.tangentTransition` — the same object as a *continuous linear
  equivalence*, whose inverse is `D(φ_ji)(φ_ij y)`; invertibility is derived from the
  primitive's own inversion law by the chain rule, not assumed;
* `EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition` — **the
  principal theorem**: for two charts of the *actual* Task-33 atlas, Mathlib's genuine
  tangent-bundle coordinate change `(tangentBundleCore …).coordChange` at a point of the
  overlap *is* `D(φ_ij)`.  Nothing is quoted from the general theory: the specialization to
  the `pieceChart`/`chartOfPoint` atlas produced in Tasks 32–33 is proved.

## The anti-shortcut clause (Task 34 §4)

Mathlib implements `TangentSpace I x` by the model vector space, so for this manifold there
*is* a definitional identification `TangentSpace localModelI x = LocalModel`.  It is recorded
below as `EmergentBase.tangentSpace_eq_localModel` and explicitly labelled as an
**implementation artefact**: it is a type-level statement about one point, it involves no
chart comparison, and it is *not* used as the proof of any coupling statement in this layer.
The invariant content is exactly the transition law proved here, i.e. how tangent vectors
transform between two charts of the actual atlas; that is what the later modules compare
with the internal Lorentz transition.

## Firewall

The import closure of this module is `Mathlib` together with the E1 Clifford/Spin core and
the base-free `Emergent` modules.  It contains no cover-over-`X`, Čech, obstruction,
Spin-native, frame-geometry or comparison module; in particular it does **not** reach
`RequestProject.Spine.Geometry.FrameField` or
`RequestProject.Spine.Geometry.TangentInstance`, the top-down branch, which is a
certification target of Task 34 and never an input.
-/

noncomputable section

namespace EmergentBase

universe t

/-- The boundaryless model with corners of the emergent manifold: the local model on
itself.  This is the model Task 33 used to state `IsManifold`. -/
abbrev localModelI : ModelWithCorners ℝ LocalModel LocalModel :=
  modelWithCornersSelf ℝ LocalModel

/-- **IMPLEMENTATION ARTEFACT, NOT A SOLDER FORM (Task 34 §4).**  Mathlib represents the
tangent space of a manifold by its model vector space, so for the emergent manifold the
tangent space at a point is *definitionally* the local model.

This is a statement about one point and one type; it involves no chart, no overlap and no
transition law, and it is therefore not a geometric identification of the internal Lorentz
model with `TM`.  It is deliberately proved here, once, so that later modules can point at
it when they explain why it is **not** used: no theorem of the Task-34 solder layer is
proved by `rfl`, by `LinearEquiv.refl` or by a tangent-space cast. -/
theorem tangentSpace_eq_localModel {ι : Type t} (B : BaseGluingData LocalModel ι)
    (x : BaseGluingData.Space B) : TangentSpace localModelI x = LocalModel := rfl

namespace BaseGluingData

variable {ι : Type t} (B : BaseGluingData LocalModel ι)

/-! ## The derivative of the primitive identification maps -/

/-- **NEWLY DEFINED (Task 34), the candidate tangent transition.**  The derivative of the
base-gluing primitive's identification map `φ_ij` on its incidence domain `W i j`.  It is
a genuine derivative of the *base* transition; no tangent space and no chart occurs in the
definition. -/
def tangentTransitionMap (i j : ι) (y : LocalModel) : LocalModel →L[ℝ] LocalModel :=
  fderivWithin ℝ (B.φ i j) (B.W i j) y

variable {B}

theorem contDiffAt_φ (h : B.SmoothGluing) {i j : ι} {y : LocalModel} (hy : y ∈ B.W i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (B.φ i j) y :=
  (h i j).contDiffAt ((B.isOpen_W i j).mem_nhds hy)

theorem differentiableAt_φ (h : B.SmoothGluing) {i j : ι} {y : LocalModel}
    (hy : y ∈ B.W i j) : DifferentiableAt ℝ (B.φ i j) y :=
  (contDiffAt_φ h hy).differentiableAt (by simp)

/-- **DERIVED (Task 34).**  On the (open) incidence domain the restricted derivative is the
genuine derivative. -/
theorem hasFDerivAt_φ (h : B.SmoothGluing) {i j : ι} {y : LocalModel} (hy : y ∈ B.W i j) :
    HasFDerivAt (B.φ i j) (B.tangentTransitionMap i j y) y := by
  rw [tangentTransitionMap, fderivWithin_of_isOpen (B.isOpen_W i j) hy]
  exact (differentiableAt_φ h hy).hasFDerivAt

/-- **DERIVED (Task 34).**  The two derivatives on an incidence domain are mutually inverse:
this comes from the primitive's own inversion law `φ_ji ∘ φ_ij = id`, by the chain rule. -/
theorem tangentTransitionMap_left_inv (h : B.SmoothGluing) {i j : ι} {y : LocalModel}
    (hy : y ∈ B.W i j) (v : LocalModel) :
    B.tangentTransitionMap j i (B.φ i j y) (B.tangentTransitionMap i j y v) = v := by
  have hcomp : HasFDerivAt (B.φ j i ∘ B.φ i j)
      ((B.tangentTransitionMap j i (B.φ i j y)).comp (B.tangentTransitionMap i j y)) y :=
    (hasFDerivAt_φ h (B.φ_mapsTo i j hy)).comp y (hasFDerivAt_φ h hy)
  have hid : HasFDerivAt (B.φ j i ∘ B.φ i j) (ContinuousLinearMap.id ℝ LocalModel) y := by
    refine (hasFDerivAt_id y).congr_of_eventuallyEq ?_
    filter_upwards [(B.isOpen_W i j).mem_nhds hy] with z hz
    exact B.φ_inv i j z hz
  have := hcomp.unique hid
  simpa using congrArg (fun f : LocalModel →L[ℝ] LocalModel => f v) this

/-- **NEWLY DEFINED (Task 34), PRINCIPAL — the tangent transition as an equivalence.**  For
a smooth base-gluing datum the derivative of the identification map at a point of the
incidence domain is a continuous linear automorphism of the local model, with inverse the
derivative of the inverse identification at the image point. -/
def tangentTransition (h : B.SmoothGluing) (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) :
    LocalModel ≃L[ℝ] LocalModel :=
  ContinuousLinearEquiv.equivOfInverse (B.tangentTransitionMap i j y)
    (B.tangentTransitionMap j i (B.φ i j y))
    (fun v => tangentTransitionMap_left_inv h hy v)
    (fun v => by
      have hy' : B.φ i j y ∈ B.W j i := B.φ_mapsTo i j hy
      have := tangentTransitionMap_left_inv h hy' v
      rwa [B.φ_inv i j y hy] at this)

@[simp] theorem tangentTransition_apply (h : B.SmoothGluing) (i j : ι) {y : LocalModel}
    (hy : y ∈ B.W i j) (v : LocalModel) :
    tangentTransition h i j hy v = B.tangentTransitionMap i j y v := rfl

/-! ## The genuine tangent coordinate change of the Task-33 atlas -/

section Atlas

variable (B)

/-- **DERIVED (Task 34), PRINCIPAL — the tangent transition of the actual atlas is the
derivative of the base transition.**

`tangentBundleCore` is Mathlib's genuine tangent-bundle construction: its coordinate changes
are the derivatives of the coordinate changes of the manifold's own atlas.  This theorem
computes them for the *actual* Task-33 atlas of the emergent manifold: between the charts of
the pieces `i` and `j`, at a point of the emergent base coming from the incidence domain
`W i j`, the tangent coordinate change is exactly `D(φ_ij)`, the derivative of the
base-gluing primitive's identification map.

The proof uses the Task-33 identification of the coordinate changes of the reconstructed
atlas (`transition_source`, `transition_apply`); it does not quote the general theory. -/
theorem tangentTransition_eq_derivative_baseTransition (h : B.SmoothGluing) {i j : ι}
    (hi : Nonempty (B.D i : Set LocalModel)) (hj : Nonempty (B.D j : Set LocalModel))
    (mi : B.pieceChart i hi ∈ atlas LocalModel (Space B))
    (mj : B.pieceChart j hj ∈ atlas LocalModel (Space B))
    {y : LocalModel} (hy : y ∈ B.W i j) :
    haveI : IsManifold localModelI 1 (Space B) :=
      (isManifold_of_smoothGluing h).of_le (by exact_mod_cast le_top)
    (tangentBundleCore localModelI (Space B)).coordChange
        ⟨B.pieceChart i hi, mi⟩ ⟨B.pieceChart j hj, mj⟩
        (B.chart i ⟨y, B.W_subset i j hy⟩)
      = B.tangentTransitionMap i j y := by
  haveI : IsManifold localModelI 1 (Space B) :=
    (isManifold_of_smoothGluing h).of_le (by exact_mod_cast le_top)
  have hyD : y ∈ B.D i := B.W_subset i j hy
  -- the chart coordinate of the point is `y` itself
  have hcoord : (B.pieceChart i hi).extend localModelI (B.chart i ⟨y, hyD⟩) = y := by
    simp [OpenPartialHomeomorph.extend, pieceChart_apply hi ⟨y, hyD⟩]
  rw [tangentBundleCore_coordChange, hcoord]
  have hrange : (Set.range localModelI) = (Set.univ : Set LocalModel) := by
    simp
  rw [hrange, fderivWithin_univ, tangentTransitionMap,
    fderivWithin_of_isOpen (B.isOpen_W i j) hy]
  -- near `y` the chart coordinate change is the primitive identification map
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(B.isOpen_W i j).mem_nhds hy] with z hz
  have hzD : z ∈ B.D i := B.W_subset i j hz
  show (B.pieceChart j hj).extend localModelI
      (((B.pieceChart i hi).extend localModelI).symm z) = B.φ i j z
  have h1 : ((B.pieceChart i hi).extend localModelI).symm z = B.chart i ⟨z, hzD⟩ := by
    simp [OpenPartialHomeomorph.extend, pieceChart_symm_apply hi hzD]
  rw [h1, B.chart_eq_chart_of_mem_W i j hz]
  simp [OpenPartialHomeomorph.extend,
    pieceChart_apply hj ⟨B.φ i j z, B.W_subset j i (B.φ_mapsTo i j hz)⟩]

/-- **DERIVED (Task 34).**  The same statement for two arbitrary members of the Task-33
atlas: every coordinate change of the genuine tangent bundle of the emergent manifold is the
derivative of one of the primitive's identification maps. -/
theorem exists_tangentTransition_of_mem_atlas (h : B.SmoothGluing)
    (e e' : atlas LocalModel (Space B)) :
    ∃ (i j : ι) (hi : Nonempty (B.D i : Set LocalModel))
      (hj : Nonempty (B.D j : Set LocalModel)),
      e.1 = B.pieceChart i hi ∧ e'.1 = B.pieceChart j hj ∧
      ∀ {y : LocalModel} (hy : y ∈ B.W i j),
        haveI : IsManifold localModelI 1 (Space B) :=
          (isManifold_of_smoothGluing h).of_le (by exact_mod_cast le_top)
        (tangentBundleCore localModelI (Space B)).coordChange e e'
            (B.chart i ⟨y, B.W_subset i j hy⟩)
          = B.tangentTransitionMap i j y := by
  obtain ⟨i, hi, hei⟩ := B.exists_pieceChart_of_mem_atlas e.2
  obtain ⟨j, hj, hej⟩ := B.exists_pieceChart_of_mem_atlas e'.2
  refine ⟨i, j, hi, hj, hei, hej, fun {y} hy => ?_⟩
  have he : e = (⟨B.pieceChart i hi, hei ▸ e.2⟩ : atlas LocalModel (Space B)) :=
    Subtype.ext hei
  have he' : e' = (⟨B.pieceChart j hj, hej ▸ e'.2⟩ : atlas LocalModel (Space B)) :=
    Subtype.ext hej
  rw [he, he']
  exact tangentTransition_eq_derivative_baseTransition B h hi hj _ _ hy

end Atlas

end BaseGluingData

end EmergentBase

end

/-! ## Axiom audit -/

#print axioms EmergentBase.BaseGluingData.tangentTransitionMap
#print axioms EmergentBase.BaseGluingData.tangentTransition
#print axioms EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition
#print axioms EmergentBase.BaseGluingData.exists_tangentTransition_of_mem_atlas
