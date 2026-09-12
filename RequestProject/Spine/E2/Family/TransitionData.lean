import RequestProject.Spine.E2.Family.FrameTrivialization

/-!
# Task 26, Package I: transition transformations between two local trivializations

Items 76–83.  Over the overlap of the domains of two Level-1 local fibre trivializations
`Φ`, `Ψ` the composite

`g(b) = Ψ_b ∘ Φ_b⁻¹ : Model ≃ₗᵢ[ℝ] Model`

is defined.  It preserves the metric (it is a linear isometry) and the orientation datum of
the model, hence lies in the intrinsic model group `GvisModel` (items 78–79).  The three
algebraic laws are proved with the convention

`g_ik = g_jk * g_ij`,

where the product of the group `Model ≃ₗᵢ[ℝ] Model` is composition of maps, `(f * g) x =
f (g x)` (item 80).  Only after the triple-overlap identity is proved may this be called a
cocycle; **no Čech cohomology is introduced** (items 81–82), and no continuity in `b` is
claimed, because no topology on the total fibre carrier is available (item 83).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

/-! ## The algebraic laws at one space -/

noncomputable section OneSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {o : Orientation ℝ V (Fin 3)}

@[simp] theorem gvisTransition_coe_apply {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) (x : Model) :
    (gvisTransition hφ hψ : Model ≃ₗᵢ[ℝ] Model) x = ψ (φ.symm x) := rfl

/-- **DERIVED (item 78).**  A transition transformation preserves the metric of the model. -/
theorem gvisTransition_inner {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) (x y : Model) :
    inner ℝ ((gvisTransition hφ hψ : Model ≃ₗᵢ[ℝ] Model) x)
        ((gvisTransition hφ hψ : Model ≃ₗᵢ[ℝ] Model) y) = inner ℝ x y :=
  LinearIsometryEquiv.inner_map_map _ x y

/-- **DERIVED (items 78–79).**  A transition transformation preserves the orientation datum
of the model; by construction it is an element of the intrinsic model group. -/
theorem gvisTransition_orientation {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) :
    IsOrientationPreserving modelOrient modelOrient
      (gvisTransition hφ hψ : Model ≃ₗᵢ[ℝ] Model) :=
  (gvisTransition hφ hψ).2

/-- **DERIVED (item 80).**  Identity law. -/
theorem gvisTransition_self {φ : V ≃ₗᵢ[ℝ] Model}
    (hφ hφ' : IsOrientationPreserving o modelOrient φ) : gvisTransition hφ hφ' = 1 := by
  refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
  simp

/-- **DERIVED (item 80).**  Inverse law. -/
theorem gvisTransition_symm {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) :
    gvisTransition hψ hφ = (gvisTransition hφ hψ)⁻¹ := by
  refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
  show φ (ψ.symm x) = _
  simp [gvisTransition]

/-- **DERIVED (item 80), principal.**  Triple-overlap law, in the convention
`g_ik = g_jk * g_ij`. -/
theorem gvisTransition_trans {φ ψ χ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ)
    (hχ : IsOrientationPreserving o modelOrient χ) :
    gvisTransition hφ hχ = gvisTransition hψ hχ * gvisTransition hφ hψ := by
  refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
  show χ (φ.symm x) = χ (ψ.symm (ψ (φ.symm x)))
  simp

end OneSpace

/-! ## The family-level transition transformations -/

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E}

/-- **NEWLY DEFINED (item 77), principal.**  The transition transformation at a point of the
overlap of the domains of two Level-1 local fibre trivializations.  It is an element of the
intrinsic model group `GvisModel` by construction (items 78–79). -/
noncomputable def transition {U W : Set B} (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W)
    {b : B} (hU : b ∈ U) (hW : b ∈ W) : GvisModel :=
  gvisTransition (Φ.orientation_preserving ⟨b, hU⟩) (Ψ.orientation_preserving ⟨b, hW⟩)

@[simp] theorem transition_apply {U W : Set B} (Φ : F.LocalFibreTriv U)
    (Ψ : F.LocalFibreTriv W) {b : B} (hU : b ∈ U) (hW : b ∈ W) (x : Model) :
    (transition Φ Ψ hU hW : Model ≃ₗᵢ[ℝ] Model) x
      = Ψ.iso ⟨b, hW⟩ ((Φ.iso ⟨b, hU⟩).symm x) := rfl

/-- **DERIVED (item 80), principal.**  Identity law. -/
theorem transition_self {U : Set B} (Φ : F.LocalFibreTriv U) {b : B} (hU hU' : b ∈ U) :
    transition Φ Φ hU hU' = 1 :=
  gvisTransition_self _ _

/-- **DERIVED (item 80), principal.**  Inverse law. -/
theorem transition_symm {U W : Set B} (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W)
    {b : B} (hU : b ∈ U) (hW : b ∈ W) :
    transition Ψ Φ hW hU = (transition Φ Ψ hU hW)⁻¹ :=
  gvisTransition_symm _ _

/-- **DERIVED (item 80), principal.**  Triple-overlap law, with the convention
`g_ik = g_jk * g_ij`. -/
theorem transition_trans {U W X : Set B} (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W)
    (Χ : F.LocalFibreTriv X) {b : B} (hU : b ∈ U) (hW : b ∈ W) (hX : b ∈ X) :
    transition Φ Χ hU hX = transition Ψ Χ hW hX * transition Φ Ψ hU hW :=
  gvisTransition_trans _ _ _

/-- **DERIVED, principal.**  The link between Packages G and I: on the overlap, the two
induced local frame trivializations differ exactly by the action of the transition
transformation on model frames. -/
theorem frameTrivAt_transition {U W : Set B} (Φ : F.LocalFibreTriv U)
    (Ψ : F.LocalFibreTriv W) {b : B} (hU : b ∈ U) (hW : b ∈ W) (v : F.FramePlusAt b) :
    frameTrivAt Ψ ⟨b, hW⟩ v = transition Φ Ψ hU hW • frameTrivAt Φ ⟨b, hU⟩ v := by
  refine FramePlusOf.ext fun i => ?_
  show Ψ.iso ⟨b, hW⟩ (FramePlusOf.vec v i)
      = (transition Φ Ψ hU hW : Model ≃ₗᵢ[ℝ] Model) (Φ.iso ⟨b, hU⟩ (FramePlusOf.vec v i))
  simp

end MetricOrientedRankThreeFamily

end NullSectorTask26
