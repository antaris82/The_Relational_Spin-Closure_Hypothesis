import RequestProject.Spine.Geometry.CausalAlgebra
import RequestProject.Spine.E1.Topology.LorentzTopology
import RequestProject.Spine.E2.Cech.Cover

/-!
# Task 4, WP2–WP3 : oriented, time-oriented Lorentz-orthonormal frame data and its cocycle

This module builds the geometric input of Task 4 and derives, rather than assumes, that its
transition data is a `GLor`-valued Čech 1-cocycle in exactly the sense of the Task-3 layer
(`CechSpinLift.VisibleCocycle`).

## The datum

`LorentzFrames.LorentzFrameData M Fib ι` consists of

| field | rôle | canonicality class |
|---|---|---|
| `cover` | an open cover `{U i}` of the base | `CHOSEN_COVER` |
| `metric` | a fibrewise bilinear form `g x` on the fibre `Fib x` | `GEOMETRIC_DATUM` |
| `vol` | a fibrewise alternating 4-form: the **orientation** datum | `CHOICE_OF_ORIENTATION` |
| `timeField` | a fibrewise vector, timelike for `g`: the **time-orientation** datum | `CHOICE_OF_TIME_ORIENTATION` |
| `frame` | local frames `e i x : 𝒮 ≃ₗ Fib x` | `CHOICE_OF_LOCAL_FRAME` |
| `orthonormal` | `g x (e i x u) (e i x v) = B_𝒮 u v` on `U i` | metric compatibility |
| `futureDirected` | `g x (T x) (e i x 1) > 0` on `U i` | time-orientation compatibility |
| `positivelyOriented` | `vol x (e i x b) > 0` on `U i` | orientation compatibility |
| `continuousOn_comparison` | continuity of the frame comparison on double overlaps | regularity |

The five structures the task insists on separating occur separately here:

1. *orientability* of the fibre family is the mere existence of a nowhere-degenerate `vol`;
2. a *chosen orientation* is the field `vol`;
3. *time-orientability* is the existence of a timelike `timeField`;
4. a *chosen time orientation* is the field `timeField`;
5. the *reduction* of the frame group to the proper orthochronous component is the derived
   theorem `LorentzFrameData.comparison_mem_GLor` — it uses **all three** of the metric,
   orientation and time-orientation compatibilities, and by the negative controls of
   `RequestProject.Spine.Geometry.CausalAlgebra` none of them may be dropped.

## What is derived

* `comparison_isometry`, `comparison_future`, `comparison_det_eq_one` — the three defining
  conditions of the native intrinsic target;
* `comparison_mem_GLor` — the transition functions really take values in `SpinCore.GLor`,
  *the* native proper orthochronous Lorentz group of the spine.  No identification of `GLor`
  with an externally defined `SO⁺(1,3)` is assumed anywhere;
* `frameCocycle` — the transition data as a `CechSpinLift.VisibleCocycle`, with
  `g i i = 1`, `g j i = (g i j)⁻¹` and `g i j * g j k = g i k` proved
  (`frame_transition_laws`).

## What is *not* claimed here

No spin group, no lift, no obstruction, no `w₂`; and no claim that the geometric datum
exists on a given manifold — its existence (local orthonormal frames for a given Lorentzian
metric) is an input, classified in `TASK04_AUDIT.md`.
-/

noncomputable section

namespace LorentzFrames

open SpinCore CechSpinLift

universe u v t

/-- **FRAME_CHOICE.**  The intrinsic coordinate basis of the carrier, used only as the
argument tuple of the orientation form. -/
def carrierBasis : Module.Basis (Fin 4) ℝ LorentzCarrier := Module.Basis.ofEquivFun coordEquiv

/-- **DERIVED (WP2).**  Top-degree alternating forms on the four-dimensional carrier
transform by the determinant. -/
theorem alternating_comp_det (α : LorentzCarrier [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (T : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (v : Fin 4 → LorentzCarrier) :
    α (fun k => T (v k)) = LinearMap.det T * α v := by
  conv_lhs => rw [α.eq_smul_basis_det carrierBasis]
  conv_rhs => rw [α.eq_smul_basis_det carrierBasis]
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [show (fun k => T (v k)) = T ∘ v from rfl, Module.Basis.det_comp]
  ring

/-- **DERIVED (WP2).**  The same transformation law, read through a frame: the value of a
fibrewise top form on a frame-image tuple picks up the determinant of the carrier-side
map. -/
theorem vol_comp_det {W : Type v} [AddCommGroup W] [Module ℝ W] (ω : W [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (e : LorentzCarrier ≃ₗ[ℝ] W) (T : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
    (v : Fin 4 → LorentzCarrier) :
    ω (fun k => e (T (v k))) = LinearMap.det T * ω (fun k => e (v k)) :=
  alternating_comp_det (ω.compLinearMap (e : LorentzCarrier →ₗ[ℝ] W)) T v

/-! ## The frame datum -/

/-- **NEWLY DEFINED (WP2), principal.**  Oriented, time-oriented, Lorentz-orthonormal local
frame data for a family of four-dimensional real fibres over a topological base.

`Fib` is an arbitrary family of real vector spaces; it is instantiated with the tangent
spaces of a smooth four-manifold in
`RequestProject.Spine.Geometry.TangentInstance`. -/
structure LorentzFrameData (M : Type u) [TopologicalSpace M] (Fib : M → Type v)
    [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] (ι : Type t) where
  /-- The chosen open cover of the base. -/
  cover : CechCover M ι
  /-- The fibrewise metric. -/
  metric : ∀ x, Fib x →ₗ[ℝ] Fib x →ₗ[ℝ] ℝ
  /-- The chosen orientation: a fibrewise top-degree alternating form. -/
  vol : ∀ x, (Fib x) [⋀^Fin 4]→ₗ[ℝ] ℝ
  /-- The chosen time orientation: a fibrewise timelike vector field. -/
  timeField : ∀ x, Fib x
  /-- The time-orientation field is timelike for the metric. -/
  timelike_timeField : ∀ x, 0 < metric x (timeField x) (timeField x)
  /-- The chosen local frames. -/
  frame : ι → ∀ x, LorentzCarrier ≃ₗ[ℝ] Fib x
  /-- On its patch, each frame is orthonormal: it pulls the metric back to `B_𝒮`. -/
  orthonormal : ∀ i, ∀ x ∈ cover.U i, ∀ u v : LorentzCarrier,
    metric x (frame i x u) (frame i x v) = BS u v
  /-- On its patch, each frame is future-directed. -/
  futureDirected : ∀ i, ∀ x ∈ cover.U i, 0 < metric x (timeField x) (frame i x sOne)
  /-- On its patch, each frame is positively oriented. -/
  positivelyOriented : ∀ i, ∀ x ∈ cover.U i,
    0 < vol x (fun k => frame i x (carrierBasis k))
  /-- Regularity: the frame comparison maps are continuous on the double overlaps. -/
  continuousOn_comparison : ∀ i j,
    ContinuousOn (fun x => (frame j x).trans (frame i x).symm) (cover.overlap₂ i j)

namespace LorentzFrameData

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {ι : Type t}
  (Φ : LorentzFrameData M Fib ι)

/-- The frame comparison `g_ij = e_i⁻¹ ∘ e_j`, defined at every point of the base (its
`GLor`-membership is proved only on the double overlap). -/
def comparison (i j : ι) (x : M) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier :=
  (Φ.frame j x).trans (Φ.frame i x).symm

@[simp] theorem comparison_apply (i j : ι) (x : M) (v : LorentzCarrier) :
    Φ.comparison i j x v = (Φ.frame i x).symm (Φ.frame j x v) := rfl

/-- The defining relation of the comparison map: `e_j = e_i ∘ g_ij`. -/
@[simp] theorem frame_comparison (i j : ι) (x : M) (v : LorentzCarrier) :
    Φ.frame i x (Φ.comparison i j x v) = Φ.frame j x v := by
  simp [comparison]

variable {Φ}

/-- **DERIVED (WP3).**  On the double overlap the comparison map is a `B_𝒮`-isometry. -/
theorem comparison_isometry {i j : ι} {x : M} (hx : x ∈ Φ.cover.overlap₂ i j)
    (u v : LorentzCarrier) :
    BS (Φ.comparison i j x u) (Φ.comparison i j x v) = BS u v := by
  have h1 := Φ.orthonormal i x hx.1 (Φ.comparison i j x u) (Φ.comparison i j x v)
  rw [frame_comparison, frame_comparison] at h1
  rw [← h1, Φ.orthonormal j x hx.2]

/-- **DERIVED (WP3).**  On the double overlap the comparison map is orthochronous: it sends
the intrinsic unit to a future-pointing vector.  This is exactly where the time orientation
enters. -/
theorem comparison_future {i j : ι} {x : M} (hx : x ∈ Φ.cover.overlap₂ i j) :
    0 < (Φ.comparison i j x sOne).1 := by
  set t : LorentzCarrier := (Φ.frame i x).symm (Φ.timeField x) with ht
  have hframe_t : Φ.frame i x t = Φ.timeField x := by simp [ht]
  have htime : 0 < NS t := by
    have := Φ.orthonormal i x hx.1 t t
    rw [hframe_t, BS_self] at this
    rw [← this]
    exact Φ.timelike_timeField x
  have ht1 : 0 < t.1 := by
    have h := Φ.orthonormal i x hx.1 t sOne
    rw [hframe_t, BS_sOne] at h
    rw [← h]
    exact Φ.futureDirected i x hx.1
  have hu : 0 < NS (Φ.comparison i j x sOne) := by
    rw [← BS_self, comparison_isometry hx, BS_self, NS_sOne]
    norm_num
  have hpair : 0 < BS t (Φ.comparison i j x sOne) := by
    have h := Φ.orthonormal i x hx.1 t (Φ.comparison i j x sOne)
    rw [hframe_t, frame_comparison] at h
    rw [← h]
    exact Φ.futureDirected j x hx.2
  exact fst_pos_of_BS_pos_of_timelike htime ht1 hu hpair

/-- **DERIVED (WP3).**  On the double overlap the comparison map has determinant `+1`.  This
is exactly where the orientation enters (positivity of the determinant), together with the
metric condition (which forces the determinant to be `±1`). -/
theorem comparison_det_eq_one {i j : ι} {x : M} (hx : x ∈ Φ.cover.overlap₂ i j) :
    LinearMap.det ((Φ.comparison i j x : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
      LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1 := by
  have hpos : 0 < LinearMap.det ((Φ.comparison i j x :
      LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier) := by
    have hj := Φ.positivelyOriented j x hx.2
    have hi := Φ.positivelyOriented i x hx.1
    have hpull := vol_comp_det (Φ.vol x) (Φ.frame i x)
      ((Φ.comparison i j x : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
        LorentzCarrier →ₗ[ℝ] LorentzCarrier) (fun k => carrierBasis k)
    have hfun : (fun k => Φ.frame i x
          (((Φ.comparison i j x : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
            LorentzCarrier →ₗ[ℝ] LorentzCarrier) (carrierBasis k)))
        = fun k => Φ.frame j x (carrierBasis k) := by
      funext k; exact frame_comparison Φ i j x (carrierBasis k)
    rw [hfun] at hpull
    rw [hpull] at hj
    nlinarith [hi, hj]
  exact det_eq_one_of_isometry_of_det_pos (fun u v => comparison_isometry hx u v) hpos

/-- **DERIVED_NATIVE (WP3), principal.**  The frame comparison maps of oriented,
time-oriented Lorentz-orthonormal frame data take their values in the native intrinsic
proper orthochronous target `SpinCore.GLor`. -/
theorem comparison_mem_GLor {i j : ι} {x : M} (hx : x ∈ Φ.cover.overlap₂ i j) :
    Φ.comparison i j x ∈ GLor :=
  isGLor_of_isometry_of_future_of_det_pos (fun u v => comparison_isometry hx u v)
    (comparison_future hx) (by rw [comparison_det_eq_one hx]; norm_num)

variable (Φ)

open scoped Classical in
/-- **NEWLY DEFINED (WP3), principal.**  The `GLor`-valued transition function of the frame
data.  Off the double overlap — where the frames carry no compatibility and the comparison
need not be Lorentzian — it is set to the unit; every statement below is about the
overlap. -/
def transition (i j : ι) (x : M) : ↥GLor :=
  if h : x ∈ Φ.cover.overlap₂ i j then ⟨Φ.comparison i j x, comparison_mem_GLor h⟩ else 1

theorem transition_val_of_mem {i j : ι} {x : M} (hx : x ∈ Φ.cover.overlap₂ i j) :
    ((Φ.transition i j x : ↥GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)
      = Φ.comparison i j x := by
  classical
  rw [transition, dif_pos hx]

/-- **DERIVED (WP3).**  The exact Čech 1-cocycle law of the frame transition data, from
`e_i⁻¹ e_j · e_j⁻¹ e_k = e_i⁻¹ e_k`. -/
theorem transition_cocycle (i j k : ι) (x : M) (hx : x ∈ Φ.cover.overlap₃ i j k) :
    Φ.transition i j x * Φ.transition j k x = Φ.transition i k x := by
  have hij : x ∈ Φ.cover.overlap₂ i j := Φ.cover.overlap₃_subset_ij i j k hx
  have hjk : x ∈ Φ.cover.overlap₂ j k := Φ.cover.overlap₃_subset_jk i j k hx
  have hik : x ∈ Φ.cover.overlap₂ i k := Φ.cover.overlap₃_subset_ik i j k hx
  apply Subtype.ext
  rw [Subgroup.coe_mul, transition_val_of_mem Φ hij, transition_val_of_mem Φ hjk,
    transition_val_of_mem Φ hik]
  apply LinearEquiv.ext
  intro v
  show Φ.comparison i j x (Φ.comparison j k x v) = Φ.comparison i k x v
  simp

/-- **DERIVED (WP3).**  Continuity of the transition data on the double overlaps, from the
regularity field of the frame datum. -/
theorem continuousOn_transition (i j : ι) :
    ContinuousOn (Φ.transition i j) (Φ.cover.overlap₂ i j) := by
  have hind : Topology.IsInducing
      (Subtype.val : ↥GLor → (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)) :=
    Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  refine (Φ.continuousOn_comparison i j).congr fun x hx => ?_
  exact transition_val_of_mem Φ hx

/-- **NEWLY DEFINED (WP3), principal endpoint — the Lorentz frame transition cocycle.**
The `GLor`-valued transition data of the frame field, as an object of the Task-3 layer. -/
def frameCocycle : VisibleCocycle (↥GLor) Φ.cover where
  g := Φ.transition
  continuousOn_g := Φ.continuousOn_transition
  cocycle i j k x hx := Φ.transition_cocycle i j k x hx

@[simp] theorem frameCocycle_g (i j : ι) : Φ.frameCocycle.g i j = Φ.transition i j := rfl

/-- **WP3, packaged endpoint.**  The three transition laws.  Only the cocycle law is proved
directly from the frames; the unit and inverse laws are inherited from the Task-3 layer,
where they are *derived* from the cocycle law. -/
theorem frame_transition_laws :
    (∀ i, ∀ x ∈ Φ.cover.U i, Φ.transition i i x = 1) ∧
    (∀ i j, ∀ x ∈ Φ.cover.overlap₂ i j, Φ.transition j i x = (Φ.transition i j x)⁻¹) ∧
    (∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k,
      Φ.transition i j x * Φ.transition j k x = Φ.transition i k x) :=
  Φ.frameCocycle.visible_transition_laws

end LorentzFrameData

end LorentzFrames
