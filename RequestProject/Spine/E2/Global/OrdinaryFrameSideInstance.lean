import RequestProject.Spine.E2.Global.PresentationIndependence

/-!
# Task 30, Package K: the inherited Task-XXVII ordinary frame side, instantiated

Items 86–88.  The two interfaces `OrdinaryFrameModel` and `OrdinaryFrameSide` frozen in
Package A are *inhabited by the inherited data*: every field below is an already proved
Task-XXVI/XXVII theorem, re-exposed under the interface name.  No new mathematics is
introduced here beyond the single elementary identity `frameIsom modelFrame = id`, needed to
compare the inherited left action of the visible group on the model frame space with the
inherited right action at the reference frame.

* `task27FrameModel` — the model frame space `FramePlusModel` with the inherited continuous
  left action of `GvisModel`, its freeness and transitivity, the inherited right action
  `frameRAct`, and the inherited reference frame `modelFrame`.
* `task27FrameSide` — the inherited ordinary frame total space `Total FramePlusAt` with its
  Task-XXVII atlas topology, its continuous base projection, its local product charts
  (`frameTriv`), the inherited chart transition law `frameTrivAt j = g_ij • frameTrivAt i`,
  and the inherited fibrewise right action.

Consequently the whole Task-XXX construction applies verbatim to the concrete Task-XXVII
frame family, **conditionally** on the Task-XXIX input as always.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29

universe u v t

/-! ## The inherited model frame space -/

/-- **DERIVED.**  The isometry attached to the model reference frame is the identity. -/
theorem frameIsom_modelFrame_eq_refl :
    frameIsom modelFrame = LinearIsometryEquiv.refl ℝ Model :=
  isom_ext_of_frame modelFrame fun i => by
    show frameIsom modelFrame (modelFrame.vec i) = modelFrame.vec i
    rw [← modelBasis_eq_modelFrame_vec, frameIsom_modelBasis]
    exact (modelBasis_eq_modelFrame_vec i).symm

/-- **DERIVED.**  At the model reference frame the inherited right action of the visible
group agrees with the inherited left action. -/
theorem frameRAct_modelFrame (k : GvisModel) : frameRAct modelFrame k = k • modelFrame := by
  refine FramePlusOf.ext fun i => ?_
  rw [frameRAct_vec, smul_frame_vec, frameIsom_modelFrame_eq_refl,
    ← modelBasis_eq_modelFrame_vec]
  rfl

/-- **PACKAGE K (items 86–88).**  The inherited ordinary frame model. -/
noncomputable def task27FrameModel : OrdinaryFrameModel GvisModel FramePlusModel where
  continuous_smul := continuous_gvisModel_smul_prod
  smul_existsUnique w w' := existsUnique_frameAction w w'
  ract := frameRAct
  ract_one := frameRAct_one
  ract_mul := frameRAct_mul
  ref := modelFrame
  ract_ref := frameRAct_modelFrame

/-! ## The inherited ordinary frame total space -/

section Side

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {ι : Type t} (Tf : TopologicalFrameFamily B E ι)

/-- **PACKAGE K.**  The inherited Task-XXVII ordinary transition system, read through the
Task-XXVIII packaging. -/
noncomputable def task27TransitionSystem : TransitionSystem B ι GvisModel :=
  NullSectorTask28.ofOrdinary Tf.toOrdinaryTransitionSystem

/-- **PACKAGE K (items 86–88), principal.**  The inherited Task-XXVII ordinary frame total
space is an `OrdinaryFrameSide` for the inherited transition system and the inherited frame
model.  Every field is an inherited theorem. -/
noncomputable def task27FrameSide :
    letI := Tf.frameTopology
    OrdinaryFrameSide (task27TransitionSystem Tf) task27FrameModel
      (Total Tf.family.FramePlusAt) :=
  letI := Tf.frameTopology
  { base := totalBase Tf.family.FramePlusAt
    continuous_base := Tf.continuous_frameBase
    chart := fun i => (Tf.frameTriv i).toTopologicalFrameTriv.homeo
    chart_base := fun _ _ => rfl
    chart_trans := fun i j x hi hj => Tf.frameTriv_transition i j x.1 ⟨hi, hj⟩ x.2
    ract := fun x k => ⟨x.1, frameRAct x.2 k⟩
    base_ract := fun _ _ => rfl
    chart_ract := fun i x k h _ => (Tf.frameTriv i).equivariant ⟨x.1, h⟩ x.2 k }

end Side

end NullSectorTask30
