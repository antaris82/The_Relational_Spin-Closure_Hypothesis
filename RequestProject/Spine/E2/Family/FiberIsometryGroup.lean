import RequestProject.Spine.E2.Family.FrameTotal

/-!
# Task 26, Package E: the intrinsic fibrewise visible group

Items 51–57.  The outcome recorded here is **E2**: each fibre has its *own* intrinsic
orientation-preserving isometry group

`GvisAt F b = SOOf (E b) (F.orient b)`,

it acts freely and transitively on the fibrewise frame carrier, but identifying these groups
with one fixed group is *additional data*: the comparison isomorphism below takes an
orientation-preserving isometry onto the model carrier as an input, and two such inputs give
isomorphisms differing by conjugation.

No constant structure group is assumed anywhere (item 57).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

noncomputable section OneSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **NEWLY DEFINED (item 52), principal.**  The intrinsic orientation-preserving isometry
group of the metric-oriented space `(V, o)`, as a subgroup of the group of linear isometries
of `V`.  Nothing is chosen: neither a frame nor a coordinate model occurs. -/
def SOOf (o : Orientation ℝ V (Fin 3)) : Subgroup (V ≃ₗᵢ[ℝ] V) where
  carrier := {f | IsOrientationPreserving o o f}
  mul_mem' := fun hf hg => IsOrientationPreserving.trans hg hf
  one_mem' := isOrientationPreserving_refl o
  inv_mem' := fun hf => hf.symm

theorem mem_SOOf {o : Orientation ℝ V (Fin 3)} {f : V ≃ₗᵢ[ℝ] V} :
    f ∈ SOOf o ↔ IsOrientationPreserving o o f := Iff.rfl

/-- **DERIVED.**  Determinant characterization of the intrinsic group in rank three. -/
theorem mem_SOOf_iff_det_pos [FiniteDimensional ℝ V] (hV : finrank ℝ V = 3)
    (o : Orientation ℝ V (Fin 3)) (f : V ≃ₗᵢ[ℝ] V) :
    f ∈ SOOf o ↔ 0 < LinearMap.det (f.toLinearEquiv : V →ₗ[ℝ] V) := by
  have hcard : Fintype.card (Fin 3) = finrank ℝ V := by rw [hV]; simp
  exact Orientation.map_eq_iff_det_pos o f.toLinearEquiv hcard

/-! ### The action on the frame carrier -/

/-- **NEWLY DEFINED.**  The action of the intrinsic group on the intrinsic frame carrier:
a frame is moved vector by vector. -/
def frameSMul {o : Orientation ℝ V (Fin 3)} (g : SOOf o) (v : FramePlusOf o) :
    FramePlusOf o :=
  ⟨v.onb.map (g : V ≃ₗᵢ[ℝ] V), by
    rw [OrthonormalBasis.toBasis_map, Basis.orientation_map, v.orientation_eq]
    exact g.2⟩

@[simp] theorem frameSMul_vec {o : Orientation ℝ V (Fin 3)} (g : SOOf o) (v : FramePlusOf o)
    (i : Fin 3) : (frameSMul g v).vec i = (g : V ≃ₗᵢ[ℝ] V) (v.vec i) := by
  simp [frameSMul, FramePlusOf.vec]

instance frameMulAction {o : Orientation ℝ V (Fin 3)} : MulAction (SOOf o) (FramePlusOf o) where
  smul := frameSMul
  one_smul v := by
    refine FramePlusOf.ext fun i => ?_
    show (frameSMul 1 v).vec i = v.vec i
    simp
  mul_smul g h v := by
    refine FramePlusOf.ext fun i => ?_
    show (frameSMul (g * h) v).vec i = (frameSMul g (frameSMul h v)).vec i
    simp

@[simp] theorem smul_frame_vec {o : Orientation ℝ V (Fin 3)} (g : SOOf o) (v : FramePlusOf o)
    (i : Fin 3) : (g • v).vec i = (g : V ≃ₗᵢ[ℝ] V) (v.vec i) := frameSMul_vec g v i

/-- **DERIVED (item 53), principal.**  The action is free. -/
theorem frameAction_free {o : Orientation ℝ V (Fin 3)} {g : SOOf o} {v : FramePlusOf o}
    (h : g • v = v) : g = 1 := by
  have hvec : ∀ i, (g : V ≃ₗᵢ[ℝ] V) (v.vec i) = v.vec i := by
    intro i
    have := congrArg (fun w : FramePlusOf o => w.vec i) h
    simpa using this
  have hlin : (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap = LinearMap.id := by
    refine v.basis.ext fun i => ?_
    simpa using hvec i
  refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
  have := congrArg (fun T : V →ₗ[ℝ] V => T x) hlin
  simpa using this

/-- **DERIVED (item 53), principal.**  The action is transitive. -/
theorem frameAction_transitive {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o) :
    ∃ g : SOOf o, g • v = w := by
  have hmem : frameTransport v w ∈ SOOf o := by
    have h1 : (v.onb.map (frameTransport v w)).toBasis.orientation
        = Orientation.map (Fin 3) (frameTransport v w).toLinearEquiv o := by
      rw [OrthonormalBasis.toBasis_map, Basis.orientation_map, v.orientation_eq]
    have h2 : (v.onb.map (frameTransport v w)) = w.onb := by
      refine DFunLike.ext_iff.mpr fun i => ?_
      show frameTransport v w (v.vec i) = w.vec i
      simp
    rw [h2, w.orientation_eq] at h1
    exact h1.symm
  refine ⟨⟨frameTransport v w, hmem⟩, ?_⟩
  refine FramePlusOf.ext fun i => ?_
  simp

/-- **DERIVED (items 53), principal.**  Free and transitive: there is exactly one element of
the intrinsic group carrying one frame to another. -/
theorem existsUnique_frameAction {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o) :
    ∃! g : SOOf o, g • v = w := by
  obtain ⟨g, hg⟩ := frameAction_transitive v w
  refine ⟨g, hg, fun g' hg' => ?_⟩
  have hinv : g⁻¹ • w = v := by rw [← hg, inv_smul_smul]
  have h : (g' * g⁻¹) • w = w := by rw [mul_smul, hinv, hg']
  exact mul_inv_eq_one.1 (frameAction_free h)

end OneSpace

/-! ## Fibrewise instantiation (items 51–56) -/

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **NEWLY DEFINED (item 52, Outcome E1 for each single fibre), principal.**  The intrinsic
orientation-preserving isometry group of the fibre over `b`. -/
noncomputable def GvisAt (F : MetricOrientedRankThreeFamily B E) (b : B) :
    Subgroup (E b ≃ₗᵢ[ℝ] E b) :=
  SOOf (F.orient b)

/-- The fibrewise action, transported to the fibrewise names. -/
noncomputable instance gvisAtMulAction (F : MetricOrientedRankThreeFamily B E) (b : B) :
    MulAction (F.GvisAt b) (F.FramePlusAt b) :=
  frameMulAction

/-- **DERIVED (item 53), principal.**  The intrinsic fibre group acts freely on the fibrewise
frames. -/
theorem gvisAt_free (F : MetricOrientedRankThreeFamily B E) {b : B} {g : F.GvisAt b}
    {v : F.FramePlusAt b} (h : g • v = v) : g = 1 :=
  frameAction_free h

/-- **DERIVED (item 53), principal.**  The intrinsic fibre group acts transitively on the
fibrewise frames. -/
theorem gvisAt_transitive (F : MetricOrientedRankThreeFamily B E) {b : B}
    (v w : F.FramePlusAt b) : ∃ g : F.GvisAt b, g • v = w :=
  frameAction_transitive v w

/-- **DERIVED**, the two together. -/
theorem gvisAt_existsUnique (F : MetricOrientedRankThreeFamily B E) {b : B}
    (v w : F.FramePlusAt b) : ∃! g : F.GvisAt b, g • v = w :=
  existsUnique_frameAction v w

end MetricOrientedRankThreeFamily

/-! ## The model group and the exact role of a fixed visible group (items 54–57) -/

/-- **NEWLY DEFINED.**  The orientation-preserving isometry group of the fixed model
carrier.  It is a *model*, not a structure group of the family: nothing below assumes that
the fibre groups are equal to it. -/
noncomputable def GvisModel : Subgroup (Model ≃ₗᵢ[ℝ] Model) := SOOf modelOrient

/-- The action of the model group on the model frames, under the `GvisModel` name. -/
noncomputable instance modelGvisMulAction : MulAction GvisModel (FramePlusOf modelOrient) :=
  frameMulAction

section Comparison

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **NEWLY DEFINED.**  Conjugation of the intrinsic group of `(V, o)` into the model group
along an orientation-preserving isometry `φ : V ≃ₗᵢ[ℝ] Model`.  The isomorphism *takes `φ` as
an input*: this is exactly the additional trivialization datum of item 56. -/
noncomputable def gvisCompare {o : Orientation ℝ V (Fin 3)} {φ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ) : SOOf o ≃* GvisModel where
  toFun g := ⟨φ.symm.trans ((g : V ≃ₗᵢ[ℝ] V).trans φ), by
    have h1 : IsOrientationPreserving modelOrient o φ.symm := hφ.symm
    exact (h1.trans g.2).trans hφ⟩
  invFun k := ⟨φ.trans ((k : Model ≃ₗᵢ[ℝ] Model).trans φ.symm), by
    have h1 : IsOrientationPreserving modelOrient o φ.symm := hφ.symm
    exact (hφ.trans k.2).trans h1⟩
  left_inv g := by
    refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
    simp
  right_inv k := by
    refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
    simp
  map_mul' g h := by
    refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
    simp

theorem gvisCompare_apply {o : Orientation ℝ V (Fin 3)} {φ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ) (g : SOOf o) (x : Model) :
    ((gvisCompare hφ g : Model ≃ₗᵢ[ℝ] Model) : Model → Model) x
      = φ ((g : V ≃ₗᵢ[ℝ] V) (φ.symm x)) := rfl

/-- The transition element of the model group attached to two orientation-preserving
identifications of the same fibre with the model. -/
noncomputable def gvisTransition {o : Orientation ℝ V (Fin 3)} {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) : GvisModel :=
  ⟨φ.symm.trans ψ, hφ.symm.trans hψ⟩

/-- **DERIVED (items 54–56), principal.**  Two orientation-preserving identifications of the
fibre with the model give comparison isomorphisms that differ by conjugation with the
transition element of the model group.  Hence identifying every fibre group with one fixed
group is additional trivialization data, canonical only up to conjugation. -/
theorem gvisCompare_change {o : Orientation ℝ V (Fin 3)} {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) (g : SOOf o) :
    gvisCompare hψ g
      = gvisTransition hφ hψ * gvisCompare hφ g * (gvisTransition hφ hψ)⁻¹ := by
  refine Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)
  simp [gvisCompare, gvisTransition]

/-- **DERIVED (item 56).**  The two comparison isomorphisms agree on a given element exactly
when the transition element commutes with its image: there is no canonical identification of
the intrinsic fibre group with the fixed model group. -/
theorem gvisCompare_eq_iff_commute {o : Orientation ℝ V (Fin 3)} {φ ψ : V ≃ₗᵢ[ℝ] Model}
    (hφ : IsOrientationPreserving o modelOrient φ)
    (hψ : IsOrientationPreserving o modelOrient ψ) (g : SOOf o) :
    gvisCompare hψ g = gvisCompare hφ g
      ↔ Commute (gvisTransition hφ hψ) (gvisCompare hφ g) := by
  rw [gvisCompare_change hφ hψ g, mul_inv_eq_iff_eq_mul]
  rfl

end Comparison


end NullSectorTask26
