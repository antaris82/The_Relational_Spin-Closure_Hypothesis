import RequestProject.Spine.E2.Family.FiberIsometryGroup

/-!
# Task 26, Package F: local fibre trivializations

**Hard target C, first half (items 58–64).**

A *local fibre trivialization over `U ⊆ B`* is a family of orientation-preserving linear
isometries from the fibres over `U` onto the fixed model carrier.  Following item 62 the
problem is split:

* **Level 1 (closed here).**  The set-theoretic / algebraic notion: no topology on `B` and no
  topology on the varying total fibre carrier is used.
* **Level 2 (not closed; the missing dependency is identified).**  A topological local
  trivialization presupposes a topology on the total fibre carrier `Σ b, E b`.  The only
  topology automatically available on that type is the disjoint-union topology of the fibres,
  and `sigmaTopology_makes_every_algebraic_triv_continuous` below shows that *every*
  algebraic trivialization is continuous for it.  Hence that topology carries no information
  and the correct bundle topology is genuine additional input (item 64: no topology is
  invented here to force Level 2).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

/-! ## The canonical positively oriented frame of the model carrier -/

/-- **NEWLY DEFINED.**  The standard positively oriented orthonormal frame of the model
carrier.  This is a frame of the *model*, not of any fibre. -/
noncomputable def modelFrame : FramePlusOf modelOrient :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℝ, rfl⟩

@[simp] theorem modelFrame_vec (i : Fin 3) :
    modelFrame.vec i = EuclideanSpace.single i (1 : ℝ) := by
  simp [modelFrame, FramePlusOf.vec, EuclideanSpace.basisFun_apply]

/-! ## Charts attached to a frame -/

noncomputable section OneSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **NEWLY DEFINED.**  The coordinate isometry of a frame: the linear isometry of `V` onto
the model carrier which sends the frame to the standard model frame. -/
def frameChart {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) : V ≃ₗᵢ[ℝ] Model :=
  v.onb.repr

@[simp] theorem frameChart_vec {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) (i : Fin 3) :
    frameChart v (v.vec i) = modelFrame.vec i := by
  show v.onb.repr (v.onb i) = _
  rw [OrthonormalBasis.repr_self, modelFrame_vec]

@[simp] theorem frameChart_symm_single {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o)
    (i : Fin 3) : (frameChart v).symm (EuclideanSpace.single i (1 : ℝ)) = v.vec i := by
  show v.onb.repr.symm (EuclideanSpace.single i (1 : ℝ)) = v.onb i
  rw [OrthonormalBasis.repr_symm_single]

theorem frameChart_map {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) :
    v.onb.map (frameChart v) = modelFrame.onb := by
  refine DFunLike.ext_iff.mpr fun i => ?_
  show frameChart v (v.vec i) = modelFrame.vec i
  simp

/-- **DERIVED, principal.**  The coordinate isometry of a positively oriented frame is
orientation preserving.  This is the exact sense in which a frame *is* a metric-oriented
identification with the model. -/
theorem frameChart_orientation {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) :
    IsOrientationPreserving o modelOrient (frameChart v) := by
  have h : (v.onb.map (frameChart v)).toBasis.orientation
      = Orientation.map (Fin 3) (frameChart v).toLinearEquiv o := by
    rw [OrthonormalBasis.toBasis_map, Basis.orientation_map, v.orientation_eq]
  rw [frameChart_map v] at h
  exact h.symm.trans modelFrame.orientation_eq

/-- **DERIVED.**  A linear isometry out of `V` is determined by its values on one frame. -/
theorem isom_ext_of_frame {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o) {f g : V ≃ₗᵢ[ℝ] W}
    (h : ∀ i, f (v.vec i) = g (v.vec i)) : f = g := by
  have hlin : (f.toLinearEquiv : V →ₗ[ℝ] W) = (g.toLinearEquiv : V →ₗ[ℝ] W) := by
    refine v.basis.ext fun i => ?_
    simpa using h i
  refine LinearIsometryEquiv.ext fun x => ?_
  have := congrArg (fun T : V →ₗ[ℝ] W => T x) hlin
  simpa using this

end OneSpace

/-! ## Level 1: algebraic local fibre trivializations (items 58–59, 62–63) -/

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **NEWLY DEFINED (items 58–59), principal.**  A *Level-1 (algebraic) local fibre
trivialization* of the family over the subset `U` of the base: an orientation-preserving
linear isometry of each fibre over `U` onto the fixed model carrier.  No regularity in `b` is
required, and none can be stated without a topology on the total fibre carrier. -/
structure LocalFibreTriv (F : MetricOrientedRankThreeFamily B E) (U : Set B) where
  /-- The fibrewise identification with the model carrier. -/
  iso : ∀ b : U, E (b : B) ≃ₗᵢ[ℝ] Model
  /-- Each identification preserves the orientation datum. -/
  orientation_preserving :
    ∀ b : U, IsOrientationPreserving (F.orient (b : B)) modelOrient (iso b)

/-- **DERIVED, principal.**  Level-1 local trivializations exist over every subset of the
base: fibrewise frames exist, and every frame gives a chart.  Note that this uses the axiom
of choice to pick a frame over each point of `U`, and that it is exactly the *global*
statement which is **not** claimed: nothing here is continuous in `b`, because no topology on
the total fibre carrier has been introduced. -/
noncomputable def localFibreTrivOfFrames (F : MetricOrientedRankThreeFamily B E) (U : Set B)
    (s : ∀ b : U, F.FramePlusAt (b : B)) : F.LocalFibreTriv U where
  iso b := frameChart (s b)
  orientation_preserving b := frameChart_orientation (s b)

theorem exists_localFibreTriv (F : MetricOrientedRankThreeFamily B E) (U : Set B) :
    Nonempty (F.LocalFibreTriv U) :=
  ⟨F.localFibreTrivOfFrames U fun _ => Classical.arbitrary _⟩

end MetricOrientedRankThreeFamily

/-! ## Level 2: the missing topological input (items 60–64) -/

section LevelTwo

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace B]

/-- **NEGATIVE CONTROL (items 61, 64, 105), principal.**  For the topology that the total
fibre carrier `Σ b, E b` carries automatically, *every* algebraic family of fibrewise
continuous maps into the model is continuous.  Consequently that topology imposes no
condition whatsoever on a trivialization: Level 2 cannot be reached by using it, and a
correct bundle topology is additional input, not a consequence of the family data. -/
theorem sigmaTopology_makes_every_algebraic_triv_continuous
    (f : ∀ b : B, E b ≃ₗᵢ[ℝ] Model) :
    Continuous (fun x : Σ b : B, E b => ((x.1 : B), f x.1 x.2)) := by
  rw [continuous_sigma_iff]
  intro i
  exact continuous_const.prodMk (f i).continuous

end LevelTwo

end NullSectorTask26
