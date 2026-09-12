import RequestProject.Spine.E2.Topology.ContinuousTransitions

/-!
# Task 27, Package I (algebraic half): the model-group action on frame spaces and the
pointwise reverse reconstruction

**Hard target C, algebraic part (items 79–85, 87).**

To state the converse question of item 81 the notion of *frame trivialization* must carry
equivariance (item 80).  The relevant action is the **right** action of the fixed visible
model group on an intrinsic frame space: a frame `v` of `(V, o)` is the same thing as an
orientation-preserving isometry `frameIsom v : Model ≃ₗᵢ V`, and `k ∈ GvisModel` acts by
precomposition,

`frameIsom (v ⋆ k) = frameIsom v ∘ k`.

The action is free and transitive (`existsUnique_frameRAct`), the frame equivalence induced
by an orientation-preserving isometry is equivariant
(`frameEquivOfIsom_frameRAct`), and — the reverse reconstruction at one point — **every**
equivariant map of frame spaces comes from a unique orientation-preserving isometry
(`existsUnique_isom_of_equivariant`).  Without equivariance this fails (item 118): a bare
bijection of frame spaces carries no linear information; see the negative control at the end.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

noncomputable section OneSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-! ## The right action of the visible model group on a frame space -/

/-- **NEWLY DEFINED (items 79–80), principal.**  The right action of the fixed visible model
group on the intrinsic frame space of a metric-oriented three-dimensional space: `v ⋆ k` is
the frame whose associated isometry is `frameIsom v ∘ k`. -/
def frameRAct {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) (k : GvisModel) :
    FramePlusOf o :=
  frameEquivOfIsom (k.2.trans (frameIsom_orientation v)) modelFrame

@[simp] theorem frameRAct_vec {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) (k : GvisModel)
    (i : Fin 3) :
    FramePlusOf.vec (frameRAct v k) i
      = frameIsom v ((k : Model ≃ₗᵢ[ℝ] Model) (modelBasis i)) := by
  show ((k : Model ≃ₗᵢ[ℝ] Model).trans (frameIsom v)) (FramePlusOf.vec modelFrame i) = _
  rw [← modelBasis_eq_modelFrame_vec]
  rfl

/-- **DERIVED, principal.**  The defining property of the action in terms of the associated
isometries. -/
theorem frameIsom_frameRAct {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) (k : GvisModel) :
    frameIsom (frameRAct v k) = (k : Model ≃ₗᵢ[ℝ] Model).trans (frameIsom v) := by
  refine isom_ext_of_frame modelFrame fun i => ?_
  rw [← modelBasis_eq_modelFrame_vec, frameIsom_modelBasis, frameRAct_vec]
  rfl

theorem frameRAct_one {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) :
    frameRAct v 1 = v := by
  refine FramePlusOf.ext fun i => ?_
  rw [frameRAct_vec]
  show frameIsom v (modelBasis i) = _
  rw [frameIsom_modelBasis]

theorem frameRAct_mul {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) (k l : GvisModel) :
    frameRAct (frameRAct v k) l = frameRAct v (k * l) := by
  refine FramePlusOf.ext fun i => ?_
  rw [frameRAct_vec, frameRAct_vec, frameIsom_frameRAct]
  rfl

/-- The unique group element carrying one frame to another. -/
def frameTransporter {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o) : GvisModel :=
  ⟨(frameIsom w).trans (frameIsom v).symm,
    (frameIsom_orientation w).trans (frameIsom_orientation v).symm⟩

@[simp] theorem frameTransporter_apply {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o)
    (m : Model) :
    (frameTransporter v w : Model ≃ₗᵢ[ℝ] Model) m = (frameIsom v).symm (frameIsom w m) := rfl

/-- **DERIVED, principal.**  The action is transitive. -/
theorem frameRAct_transporter {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o) :
    frameRAct v (frameTransporter v w) = w := by
  refine FramePlusOf.ext fun i => ?_
  rw [frameRAct_vec, frameTransporter_apply, LinearIsometryEquiv.apply_symm_apply,
    frameIsom_modelBasis]

/-- **DERIVED, principal.**  The action is free. -/
theorem frameRAct_left_injective {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o)
    {k l : GvisModel} (h : frameRAct v k = frameRAct v l) : k = l := by
  refine Subtype.ext (isom_ext_of_frame modelFrame fun i => ?_)
  have hi := congrArg (fun w : FramePlusOf o => FramePlusOf.vec w i) h
  simp only [frameRAct_vec] at hi
  have := (frameIsom v).injective hi
  rw [← modelBasis_eq_modelFrame_vec]
  exact this

/-- **DERIVED, principal.**  Free and transitive: exactly one group element carries a given
frame to a given frame. -/
theorem existsUnique_frameRAct {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o) :
    ∃! k : GvisModel, frameRAct v k = w :=
  ⟨frameTransporter v w, frameRAct_transporter v w, fun _ h =>
    frameRAct_left_injective v (h.trans (frameRAct_transporter v w).symm)⟩

/-! ## Equivariance of the induced frame equivalences -/

theorem frameIsom_frameEquivOfIsom {oV : Orientation ℝ V (Fin 3)} {oW : Orientation ℝ W (Fin 3)}
    {f : V ≃ₗᵢ[ℝ] W} (hf : IsOrientationPreserving oV oW f) (v : FramePlusOf oV) :
    frameIsom (frameEquivOfIsom hf v) = (frameIsom v).trans f := by
  refine isom_ext_of_frame modelFrame fun i => ?_
  rw [← modelBasis_eq_modelFrame_vec]
  show frameIsom (frameEquivOfIsom hf v) (modelBasis i) = f (frameIsom v (modelBasis i))
  rw [frameIsom_modelBasis, frameIsom_modelBasis, frameEquivOfIsom_vec]

/-- **DERIVED (item 80), principal.**  The frame equivalence induced by an
orientation-preserving isometry is equivariant for the right action of the model group. -/
theorem frameEquivOfIsom_frameRAct {oV : Orientation ℝ V (Fin 3)}
    {oW : Orientation ℝ W (Fin 3)} {f : V ≃ₗᵢ[ℝ] W} (hf : IsOrientationPreserving oV oW f)
    (v : FramePlusOf oV) (k : GvisModel) :
    frameEquivOfIsom hf (frameRAct v k) = frameRAct (frameEquivOfIsom hf v) k := by
  refine FramePlusOf.ext fun i => ?_
  rw [frameEquivOfIsom_vec, frameRAct_vec, frameRAct_vec, frameIsom_frameEquivOfIsom]
  rfl

/-- **DERIVED.**  Two equivariant maps of frame spaces which agree at one frame are equal. -/
theorem eq_of_equivariant {o : Orientation ℝ V (Fin 3)} {α β : FramePlusOf o → FramePlusModel}
    (hα : ∀ v k, α (frameRAct v k) = frameRAct (α v) k)
    (hβ : ∀ v k, β (frameRAct v k) = frameRAct (β v) k) {v₀ : FramePlusOf o}
    (h : α v₀ = β v₀) : α = β := by
  funext w
  obtain ⟨k, hk, -⟩ := existsUnique_frameRAct v₀ w
  rw [← hk, hα, hβ, h]

/-! ## The pointwise reverse reconstruction (items 82–85, 87) -/

/-- The candidate reconstructed identification: the orientation-preserving isometry sending
the frame `v₀` to the model frame `w₀`. -/
def isomOfFramePair {o : Orientation ℝ V (Fin 3)} (v₀ : FramePlusOf o) (w₀ : FramePlusModel) :
    V ≃ₗᵢ[ℝ] Model :=
  (frameChart v₀).trans (frameIsom w₀)

theorem isomOfFramePair_orientation {o : Orientation ℝ V (Fin 3)} (v₀ : FramePlusOf o)
    (w₀ : FramePlusModel) :
    IsOrientationPreserving o modelOrient (isomOfFramePair v₀ w₀) :=
  (frameChart_orientation v₀).trans (frameIsom_orientation w₀)

theorem frameEquivOfIsom_isomOfFramePair {o : Orientation ℝ V (Fin 3)} (v₀ : FramePlusOf o)
    (w₀ : FramePlusModel) :
    frameEquivOfIsom (isomOfFramePair_orientation v₀ w₀) v₀ = w₀ := by
  refine FramePlusOf.ext fun i => ?_
  rw [frameEquivOfIsom_vec]
  show frameIsom w₀ (frameChart v₀ (FramePlusOf.vec v₀ i)) = _
  rw [frameChart_vec, ← modelBasis_eq_modelFrame_vec, frameIsom_modelBasis]

/-- **DERIVED (items 82–85, 87), principal.**  Reverse reconstruction at one metric-oriented
space: an **equivariant** map from the intrinsic frame space to the model frame space is
induced by exactly one orientation-preserving linear isometry onto the model.  Linearity,
metric preservation and orientation preservation of the reconstruction are part of the
statement (the reconstructed object is a `≃ₗᵢ` satisfying `IsOrientationPreserving`). -/
theorem existsUnique_isom_of_equivariant {o : Orientation ℝ V (Fin 3)}
    (Θ : FramePlusOf o → FramePlusModel)
    (hΘ : ∀ v k, Θ (frameRAct v k) = frameRAct (Θ v) k) (v₀ : FramePlusOf o) :
    ∃! f : {f : V ≃ₗᵢ[ℝ] Model // IsOrientationPreserving o modelOrient f},
      ∀ v, frameEquivOfIsom f.2 v = Θ v := by
  refine ⟨⟨isomOfFramePair v₀ (Θ v₀), isomOfFramePair_orientation v₀ (Θ v₀)⟩, ?_, ?_⟩
  · have h := eq_of_equivariant
      (α := fun v => frameEquivOfIsom (isomOfFramePair_orientation v₀ (Θ v₀)) v) (β := Θ)
      (fun v k => frameEquivOfIsom_frameRAct _ v k) hΘ
      (v₀ := v₀) (frameEquivOfIsom_isomOfFramePair v₀ (Θ v₀))
    intro v
    exact congrFun h v
  · rintro ⟨g, hg⟩ hgΘ
    refine Subtype.ext (isom_ext_of_frame v₀ fun i => ?_)
    have h1 : frameEquivOfIsom hg v₀ = Θ v₀ := hgΘ v₀
    have h2 : frameEquivOfIsom (isomOfFramePair_orientation v₀ (Θ v₀)) v₀ = Θ v₀ :=
      frameEquivOfIsom_isomOfFramePair v₀ (Θ v₀)
    have := congrArg (fun w : FramePlusModel => FramePlusOf.vec w i) (h1.trans h2.symm)
    simpa using this

/-! ## Negative control (item 118): equivariance cannot be dropped -/

theorem frameIsom_modelFrame : frameIsom modelFrame = LinearIsometryEquiv.refl ℝ Model := by
  refine isom_ext_of_frame modelFrame fun i => ?_
  rw [← modelBasis_eq_modelFrame_vec, frameIsom_modelBasis, modelBasis_eq_modelFrame_vec]
  rfl

/-- The positively oriented model frame obtained by cyclically reindexing the standard
frame. -/
def cycFrame : FramePlusModel :=
  ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).reindex cyc3, reindex_cyc3_orientation⟩

theorem cycFrame_vec (i : Fin 3) :
    FramePlusOf.vec cycFrame i = modelBasis (cyc3.symm i) := by
  show ((EuclideanSpace.basisFun (Fin 3) ℝ).reindex cyc3) i = _
  rw [OrthonormalBasis.reindex_apply]

/-- The three-cycle element of the visible model group. -/
def cycElt : GvisModel := frameTransporter modelFrame cycFrame

theorem cycElt_modelBasis (i : Fin 3) :
    (cycElt : Model ≃ₗᵢ[ℝ] Model) (modelBasis i) = modelBasis (cyc3.symm i) := by
  rw [cycElt, frameTransporter_apply, frameIsom_modelFrame]
  show (LinearIsometryEquiv.refl ℝ Model).symm (frameIsom cycFrame (modelBasis i)) = _
  rw [frameIsom_modelBasis, cycFrame_vec]
  rfl

theorem modelBasis_ne {i j : Fin 3} (h : i ≠ j) : modelBasis i ≠ modelBasis j := by
  intro hij
  have hval := congrFun (congrArg (fun m : Model => (m : Fin 3 → ℝ)) hij) i
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, h] at hval

theorem cycElt_sq_ne_one : cycElt * cycElt ≠ 1 := by
  intro h
  have h0 : ((cycElt * cycElt : GvisModel) : Model ≃ₗᵢ[ℝ] Model) (modelBasis 0)
      = modelBasis (cyc3.symm (cyc3.symm 0)) := by
    show (cycElt : Model ≃ₗᵢ[ℝ] Model) ((cycElt : Model ≃ₗᵢ[ℝ] Model) (modelBasis 0)) = _
    rw [cycElt_modelBasis, cycElt_modelBasis]
  rw [h] at h0
  have h1 : cyc3.symm (cyc3.symm 0) = 2 := by decide
  rw [h1] at h0
  have hone : ((1 : GvisModel) : Model ≃ₗᵢ[ℝ] Model) (modelBasis 0) = modelBasis 0 := rfl
  rw [hone] at h0
  exact modelBasis_ne (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) h0

/-- **NEGATIVE CONTROL (item 118), principal.**  Equivariance in the definition of a
compatible frame trivialization cannot be dropped: the transposition of two distinct model
frames is a bijection of the model frame space which is **not** equivariant for the
model-group action, hence (by `frameEquivOfIsom_frameRAct`) is not induced by any
orientation-preserving isometry.  A bare frame bijection therefore carries no fibrewise
linear information. -/
theorem exists_nonequivariant_frame_bijection :
    ∃ σ : FramePlusModel ≃ FramePlusModel,
      ¬ ∀ (v : FramePlusModel) (k : GvisModel), σ (frameRAct v k) = frameRAct (σ v) k := by
  classical
  have hc : frameRAct modelFrame cycElt = cycFrame :=
    frameRAct_transporter modelFrame cycFrame
  refine ⟨Equiv.swap modelFrame cycFrame, ?_⟩
  intro hequiv
  have hstep : Equiv.swap modelFrame cycFrame (frameRAct modelFrame cycElt)
      = frameRAct (Equiv.swap modelFrame cycFrame modelFrame) cycElt := hequiv modelFrame cycElt
  rw [hc, Equiv.swap_apply_left, Equiv.swap_apply_right] at hstep
  rw [← hc, frameRAct_mul] at hstep
  refine cycElt_sq_ne_one (frameRAct_left_injective modelFrame ?_)
  rw [frameRAct_one, ← hstep]

end OneSpace

end NullSectorTask27
