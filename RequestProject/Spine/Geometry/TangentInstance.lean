import RequestProject.Spine.Geometry.SpinStructure

/-!
# Task 4, WP1/WP3 : the tangent-bundle instance on a smooth four-manifold

The abstract fibre family of `RequestProject.Spine.Geometry.FrameField` is instantiated here
with the **genuine Mathlib tangent spaces** `Bundle.TangentSpace` of a smooth manifold
modelled on the intrinsic carrier `𝒮 = LorentzCarrier = ℝ × (Fin 3 → ℝ)`, which is a real
vector space of dimension exactly `4` (`finrank_carrier`).  So `M` really is a smooth
four-dimensional manifold and `Fib x` really is `T_x M`.

## Availability audit (WP1), summarised

Present in the pinned Mathlib and used here: charted spaces, models with corners, smooth
manifolds (`IsManifold`), `Bundle.TangentSpace` / `TangentBundle`, vector bundles, local
frames of a vector bundle, `Module.Basis`, `AlternatingMap` and `LinearMap.det`.

Absent from the pinned Mathlib, and therefore either built natively here or classified as
blocked in `TASK04_AUDIT.md`: pseudo-Riemannian and Lorentzian metrics, time orientation,
manifold orientation, (orthonormal) frame bundles, principal bundles, Spin structures,
Stiefel–Whitney classes, and Čech or singular cohomology with `ℤ₂` coefficients in a form
usable for a topological space.  The Lorentzian metric, the orientation, the time
orientation and the orthonormal local frames are supplied natively by
`LorentzFrames.LorentzFrameData`.

**Not claimed.**  That such frame data exists for a given Lorentzian metric.  Producing
local Lorentz-orthonormal frames from a metric requires a fibrewise Gram–Schmidt process
together with a shrinking argument; that is missing infrastructure, recorded in the audit,
and it is *not* smuggled in as a hypothesis anywhere: every theorem below is conditional on
the frame data being given.
-/

noncomputable section

namespace LorentzFrames

open SpinCore CechSpinLift NullSectorTask28

universe u t

/-- **WP9 (dimension audit).**  The intrinsic carrier is four-dimensional. -/
theorem finrank_carrier : Module.finrank ℝ LorentzCarrier = 4 := by
  simp [LorentzCarrier, Module.finrank_prod]

/-- The model with corners of a four-manifold modelled on the intrinsic carrier: the
boundaryless model `𝒮 → 𝒮`. -/
abbrev carrierModel : ModelWithCorners ℝ LorentzCarrier LorentzCarrier :=
  modelWithCornersSelf ℝ LorentzCarrier

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LorentzCarrier M]

/-- **WP9 (dimension audit).**  Every tangent space of such a manifold is four-dimensional;
this is the fibre on which the Lorentzian frame data lives. -/
theorem finrank_tangentSpace (x : M) :
    Module.finrank ℝ (TangentSpace carrierModel x) = 4 := by
  simp [TangentSpace, LorentzCarrier, Module.finrank_prod]

/-- **NEWLY DEFINED (WP3), principal.**  Oriented, time-oriented, Lorentz-orthonormal local
tangent-frame data on a manifold modelled on the intrinsic carrier: the abstract frame datum
with the fibre family taken to be the tangent spaces of `M`. -/
abbrev LorentzTangentFrameData (M : Type u) [TopologicalSpace M]
    [ChartedSpace LorentzCarrier M] (ι : Type t) : Type _ :=
  LorentzFrameData M (fun x : M => TangentSpace carrierModel x) ι

variable {ι : Type t}

/-- **DERIVED_NATIVE (WP3), packaged for the tangent bundle.**  For a *smooth* manifold `M`
modelled on the four-dimensional intrinsic carrier and oriented, time-oriented,
Lorentz-orthonormal tangent-frame data on it:

1. every tangent space is four-dimensional;
2. the frame comparison maps take values in the native proper orthochronous target `GLor`;
3. the transition data satisfies `g i i = 1`, `g j i = (g i j)⁻¹` and the exact triple
   overlap cocycle law;
4. the transition data is continuous on every double overlap.

The smoothness hypothesis is carried because the task asks for a smooth manifold; the
statements themselves are topological and do not use it. -/
theorem tangent_frame_cocycle [IsManifold carrierModel ⊤ M]
    (Φ : LorentzTangentFrameData M ι) :
    (∀ x : M, Module.finrank ℝ (TangentSpace carrierModel x) = 4) ∧
    (∀ i j, ∀ x ∈ Φ.cover.overlap₂ i j, Φ.comparison i j x ∈ GLor) ∧
    (∀ i, ∀ x ∈ Φ.cover.U i, Φ.transition i i x = 1) ∧
    (∀ i j, ∀ x ∈ Φ.cover.overlap₂ i j, Φ.transition j i x = (Φ.transition i j x)⁻¹) ∧
    (∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k,
      Φ.transition i j x * Φ.transition j k x = Φ.transition i k x) ∧
    (∀ i j, ContinuousOn (Φ.transition i j) (Φ.cover.overlap₂ i j)) :=
  ⟨finrank_tangentSpace, fun _ _ _ hx => LorentzFrameData.comparison_mem_GLor hx,
    Φ.frame_transition_laws.1, Φ.frame_transition_laws.2.1, Φ.frame_transition_laws.2.2,
    Φ.continuousOn_transition⟩

/-- **DERIVED_NATIVE (WP4+WP5), packaged for the tangent bundle — the Task-4 endpoint.**

For a smooth four-manifold `M` with oriented, time-oriented, Lorentz-orthonormal
tangent-frame data `Φ` and any family `D` of continuous local Spin representatives of the
resulting Lorentz frame transition cocycle:

1. the triple-overlap defect is `{±1}`-valued;
2. the resulting class — the **Lorentz-frame Spin-lift obstruction** — is independent of the
   choice of local Spin representatives;
3. it vanishes **iff** the Lorentz frame data admits a Spin structure, i.e. a continuous
   Spin-valued transition cocycle lifting the frame cocycle along the native double cover
   `SpinGroup → GLor`.

This class is *not* asserted to be `w₂(TM)`; see `RequestProject.Spine.Geometry.Core`. -/
theorem tangent_frame_spin_lift_obstruction [IsManifold carrierModel ⊤ M]
    (Φ : LorentzTangentFrameData M ι) (D : FrameSpinLifts Φ) :
    (∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k,
      D.defect i j k x = 1 ∨ D.defect i j k x = negOneSpin) ∧
    (∀ D' : FrameSpinLifts Φ,
      LorentzFrameData.frameObstruction D = LorentzFrameData.frameObstruction D') ∧
    (LorentzFrameData.frameObstruction D = trivialClass internalSpinProjection Φ.cover ↔
      Nonempty (SpinFrameStructure Φ)) :=
  ⟨fun _ _ _ _ hx => LorentzFrameData.frame_defect_eq_pm_one D _ _ _ hx,
    fun D' => LorentzFrameData.frameObstruction_choice_independent D D',
    LorentzFrameData.frameObstruction_eq_trivial_iff_spinStructure D⟩

end LorentzFrames
