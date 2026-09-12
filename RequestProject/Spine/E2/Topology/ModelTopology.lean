import RequestProject.Spine.E2.Family.TransitionData

/-!
# Task 27, Package A′: topologies on the fixed model data

**Inherited (Package A, items 21–23).**  Everything about the *algebraic* family — the base
`B`, the fibres `E b`, the fibre metric and orientation, the rank-three condition,
`FramePlusAt`, `FrameTotal`, `frameBase`, the algebraic local fibre trivializations, the
induced algebraic frame trivializations, the model carrier `Model`, the model frame space
`FramePlusOf modelOrient` and the algebraic transition transformations — is imported from
Task XXVI **unchanged**.  Nothing in the Task-XXVI layer is edited here (item 133); this
layer only *adds* declarations.

**New in this module (items 66, 76).**  The fixed model objects are equipped with their
topologies:

* `Model = EuclideanSpace ℝ (Fin 3)` already carries its norm topology (inherited);
* `Model ≃ₗᵢ[ℝ] Model` is equipped with the topology of pointwise convergence, and the
  visible model group `GvisModel` with the inherited subtype topology;
* the model frame space carries the topology of pointwise convergence of the three frame
  vectors.

The analytic facts proved here — joint continuity of evaluation, continuity of inversion,
continuity of the group operations and of the action on the frame space — are the only
analysis used in Task XXVII.  No smoothness, no Lie theory, no bundle infrastructure.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Module

/-! ## The standard orthonormal basis of the model, as a frame -/

/-- The standard orthonormal basis of the model carrier. -/
noncomputable abbrev modelBasis : OrthonormalBasis (Fin 3) ℝ Model :=
  EuclideanSpace.basisFun (Fin 3) ℝ

theorem modelBasis_eq_modelFrame_vec (i : Fin 3) : modelBasis i = modelFrame.vec i := by
  simp [EuclideanSpace.basisFun_apply]

/-- Expansion of a model vector in the standard orthonormal basis. -/
theorem model_sum_repr (m : Model) : ∑ i, (inner ℝ (modelBasis i) m : ℝ) • modelBasis i = m :=
  modelBasis.sum_repr' m

/-! ## The topology on the model isometry group (item 66) -/

/-- **NEWLY DEFINED (item 66).**  The topology of pointwise convergence on the isometries of
the model carrier.  It is *induced* from the ambient function space; no new analytic
structure is postulated.  (On this fixed three-dimensional carrier it coincides with the
operator-norm topology, but that identification is not needed anywhere below.) -/
instance modelIsomTopology : TopologicalSpace (Model ≃ₗᵢ[ℝ] Model) :=
  TopologicalSpace.induced (fun f => (f : Model → Model)) inferInstance

/-- The defining property of `modelIsomTopology`. -/
theorem continuous_modelIsom_iff {X : Type*} [TopologicalSpace X]
    (g : X → Model ≃ₗᵢ[ℝ] Model) : Continuous g ↔ ∀ m, Continuous fun x => g x m := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- The visible model group carries the inherited subtype topology (item 66). -/
theorem continuous_gvisModel_iff {X : Type*} [TopologicalSpace X] (g : X → GvisModel) :
    Continuous g ↔ ∀ m, Continuous fun x => (g x : Model ≃ₗᵢ[ℝ] Model) m := by
  rw [continuous_induced_rng, continuous_modelIsom_iff]
  rfl

theorem eval_expand (f : Model ≃ₗᵢ[ℝ] Model) (m : Model) :
    f m = ∑ i, (inner ℝ (modelBasis i) m : ℝ) • f (modelBasis i) := by
  conv_lhs => rw [← model_sum_repr m]
  rw [map_sum]
  simp

/-- **DERIVED, principal.**  Joint continuity of evaluation: if a family of model isometries
is continuous and a family of model vectors is continuous, the evaluated family is
continuous. -/
theorem continuous_modelIsom_eval {X : Type*} [TopologicalSpace X]
    {g : X → Model ≃ₗᵢ[ℝ] Model} (hg : Continuous g) {m : X → Model} (hm : Continuous m) :
    Continuous fun x => g x (m x) := by
  have h : (fun x => g x (m x))
      = fun x => ∑ i, (inner ℝ (modelBasis i) (m x) : ℝ) • g x (modelBasis i) := by
    funext x; exact eval_expand (g x) (m x)
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((innerSL ℝ (modelBasis i)).continuous.comp hm).smul
    (((continuous_modelIsom_iff g).1 hg) (modelBasis i))

theorem continuous_gvisModel_eval {X : Type*} [TopologicalSpace X] {g : X → GvisModel}
    (hg : Continuous g) {m : X → Model} (hm : Continuous m) :
    Continuous fun x => (g x : Model ≃ₗᵢ[ℝ] Model) (m x) :=
  continuous_modelIsom_eval (continuous_induced_dom.comp hg) hm

/-- Adjoint expansion of the inverse of a model isometry. -/
theorem inv_expand (f : Model ≃ₗᵢ[ℝ] Model) (m : Model) :
    f.symm m = ∑ i, (inner ℝ (f (modelBasis i)) m : ℝ) • modelBasis i := by
  have hmap : ∀ i, (modelBasis.map f) i = f (modelBasis i) := fun _ => rfl
  have h : ∑ i, (inner ℝ (f (modelBasis i)) m : ℝ) • f (modelBasis i) = m := by
    have := (modelBasis.map f).sum_repr' m
    simpa [hmap] using this
  calc f.symm m = f.symm (∑ i, (inner ℝ (f (modelBasis i)) m : ℝ) • f (modelBasis i)) := by
        rw [h]
    _ = ∑ i, (inner ℝ (f (modelBasis i)) m : ℝ) • modelBasis i := by
        rw [map_sum]; simp

/-- **DERIVED, principal.**  Continuity of inversion, jointly with a continuous family of
model vectors. -/
theorem continuous_modelIsom_symm_eval {X : Type*} [TopologicalSpace X]
    {g : X → Model ≃ₗᵢ[ℝ] Model} (hg : Continuous g) {m : X → Model} (hm : Continuous m) :
    Continuous fun x => (g x).symm (m x) := by
  have h : (fun x => (g x).symm (m x))
      = fun x => ∑ i, (inner ℝ (g x (modelBasis i)) (m x) : ℝ) • modelBasis i := by
    funext x; exact inv_expand (g x) (m x)
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  refine Continuous.smul ?_ continuous_const
  exact continuous_inner.comp ((((continuous_modelIsom_iff g).1 hg) (modelBasis i)).prodMk hm)

/-- **DERIVED (item 66).**  Multiplication of the model group is continuous. -/
instance : ContinuousMul GvisModel := by
  constructor
  rw [continuous_gvisModel_iff]
  intro m
  have h1 : Continuous fun p : GvisModel × GvisModel => (p.2 : Model ≃ₗᵢ[ℝ] Model) m :=
    continuous_gvisModel_eval continuous_snd continuous_const
  exact continuous_gvisModel_eval continuous_fst h1

/-- **DERIVED (item 66).**  Inversion of the model group is continuous. -/
instance : ContinuousInv GvisModel := by
  constructor
  rw [continuous_gvisModel_iff]
  intro m
  exact continuous_modelIsom_symm_eval (continuous_induced_dom.comp continuous_id)
    continuous_const

/-- **DERIVED (item 66), principal.**  With its inherited topology the fixed visible model
group is a topological group.  Only this minimal amount of group topology is constructed;
no Lie-group development is imported. -/
instance : IsTopologicalGroup GvisModel := ⟨⟩

/-! ## The topology on frame spaces -/

section FrameTop

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **NEWLY DEFINED.**  The topology of pointwise convergence of the frame vectors on the
oriented orthonormal frame space of a metric-oriented space.  For the model this is the
topology of the model frame space `FramePlusModel` used throughout. -/
instance framePlusTopology (o : Orientation ℝ V (Fin 3)) :
    TopologicalSpace (FramePlusOf o) :=
  TopologicalSpace.induced (fun v => (fun i => FramePlusOf.vec v i : Fin 3 → V)) inferInstance

theorem continuous_framePlus_iff {X : Type*} [TopologicalSpace X]
    {o : Orientation ℝ V (Fin 3)} (g : X → FramePlusOf o) :
    Continuous g ↔ ∀ i, Continuous fun x => FramePlusOf.vec (g x) i := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

theorem continuous_framePlus_vec {o : Orientation ℝ V (Fin 3)} (i : Fin 3) :
    Continuous fun v : FramePlusOf o => FramePlusOf.vec v i :=
  ((continuous_framePlus_iff (id : FramePlusOf o → FramePlusOf o)).1 continuous_id) i

end FrameTop

/-- **NEWLY DEFINED.**  The model frame space, with the topology just defined. -/
abbrev FramePlusModel : Type := FramePlusOf modelOrient

/-! ## The isometry attached to a frame, and its continuity -/

noncomputable section FrameIsom

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **NEWLY DEFINED.**  The identification of the model with a metric-oriented space
determined by an oriented orthonormal frame: the inverse of the coordinate isometry of the
frame.  This is the "frame as an isometry" picture used for the reverse reconstruction. -/
def frameIsom {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) : Model ≃ₗᵢ[ℝ] V :=
  (frameChart v).symm

@[simp] theorem frameIsom_modelBasis {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o)
    (i : Fin 3) : frameIsom v (modelBasis i) = FramePlusOf.vec v i := by
  rw [modelBasis_eq_modelFrame_vec, modelFrame_vec]
  exact frameChart_symm_single v i

theorem frameIsom_orientation {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) :
    IsOrientationPreserving modelOrient o (frameIsom v) :=
  (frameChart_orientation v).symm

theorem frameIsom_apply {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) (m : Model) :
    frameIsom v m = ∑ i, (inner ℝ (modelBasis i) m : ℝ) • FramePlusOf.vec v i := by
  conv_lhs => rw [← model_sum_repr m]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [map_smul, frameIsom_modelBasis]

/-- **DERIVED, principal.**  The frame-to-isometry construction is jointly continuous in the
frame and in the model vector. -/
theorem continuous_frameIsom_eval {X : Type*} [TopologicalSpace X]
    {o : Orientation ℝ V (Fin 3)} {v : X → FramePlusOf o} (hv : Continuous v)
    {m : X → Model} (hm : Continuous m) : Continuous fun x => frameIsom (v x) (m x) := by
  have h : (fun x => frameIsom (v x) (m x))
      = fun x => ∑ i, (inner ℝ (modelBasis i) (m x) : ℝ) • FramePlusOf.vec (v x) i := by
    funext x; exact frameIsom_apply (v x) (m x)
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((innerSL ℝ (modelBasis i)).continuous.comp hm).smul
    (((continuous_framePlus_iff v).1 hv) i)

end FrameIsom

/-! ## Continuity of the visible action on the model frame space (item 76) -/

/-- **DERIVED (item 76), principal.**  The action of the visible model group on the model
frame space is continuous. -/
theorem continuous_gvisModel_smul {X : Type*} [TopologicalSpace X] {g : X → GvisModel}
    (hg : Continuous g) {v : X → FramePlusModel} (hv : Continuous v) :
    Continuous fun x => g x • v x := by
  rw [continuous_framePlus_iff]
  intro i
  have h : (fun x => FramePlusOf.vec (g x • v x) i)
      = fun x => (g x : Model ≃ₗᵢ[ℝ] Model) (FramePlusOf.vec (v x) i) := by
    funext x; exact smul_frame_vec (g x) (v x) i
  rw [h]
  exact continuous_gvisModel_eval hg (((continuous_framePlus_iff v).1 hv) i)

/-- **DERIVED (item 76).**  The action map of the model group on the model frame space is
continuous as a map of the product. -/
theorem continuous_gvisModel_smul_prod :
    Continuous fun p : GvisModel × FramePlusModel => p.1 • p.2 :=
  continuous_gvisModel_smul continuous_fst continuous_snd

end NullSectorTask27
