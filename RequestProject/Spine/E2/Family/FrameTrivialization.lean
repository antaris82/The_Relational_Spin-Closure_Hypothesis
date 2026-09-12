import RequestProject.Spine.E2.Family.LocalTrivialization

/-!
# Task 26, Packages G and H: induced frame trivializations and reverse reconstruction

**Hard target C, second half (items 65–75).**

Package G.  An orientation-preserving isometry of metric-oriented three-dimensional spaces
induces an equivalence of their oriented-frame carriers (`frameEquivOfIsom`), and a Level-1
local fibre trivialization over `U` therefore induces a *local frame trivialization*

`frameBase ⁻¹ U ≃ U × FramePlusOf modelOrient`

at the set level — the strongest level currently justified, since no topology on the total
carriers exists (item 67).

Package H.  The reverse reconstruction is proved exactly:

* an orientation-preserving isometry onto the model is *uniquely* determined by the image of
  one oriented orthonormal frame (item 72);
* conversely every oriented frame arises this way, so at each point the two data sets are in
  bijection (`isomEquivFrame`);
* over `U` this assembles into `LocalFibreTriv F U ≃ (∀ b : U, FramePlusAt b)` — a local
  fibre trivialization is *exactly* a local frame section (item 73: one local frame section
  is what is needed, not merely an abstract equivalence of frame spaces).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

noncomputable section OneSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **NEWLY DEFINED (items 65–66), principal.**  An orientation-preserving linear isometry
induces an equivalence of the oriented orthonormal frame carriers; by construction it
preserves oriented orthonormality, since the image datum is again a positively oriented
orthonormal basis. -/
def frameEquivOfIsom {oV : Orientation ℝ V (Fin 3)} {oW : Orientation ℝ W (Fin 3)}
    {f : V ≃ₗᵢ[ℝ] W} (hf : IsOrientationPreserving oV oW f) :
    FramePlusOf oV ≃ FramePlusOf oW where
  toFun v := ⟨v.onb.map f, by
    rw [OrthonormalBasis.toBasis_map, Basis.orientation_map, v.orientation_eq]; exact hf⟩
  invFun w := ⟨w.onb.map f.symm, by
    rw [OrthonormalBasis.toBasis_map, Basis.orientation_map, w.orientation_eq]; exact hf.symm⟩
  left_inv v := by
    refine FramePlusOf.ext fun i => ?_
    show f.symm (f (v.vec i)) = v.vec i
    simp
  right_inv w := by
    refine FramePlusOf.ext fun i => ?_
    show f (f.symm (w.vec i)) = w.vec i
    simp

@[simp] theorem frameEquivOfIsom_vec {oV : Orientation ℝ V (Fin 3)}
    {oW : Orientation ℝ W (Fin 3)} {f : V ≃ₗᵢ[ℝ] W} (hf : IsOrientationPreserving oV oW f)
    (v : FramePlusOf oV) (i : Fin 3) : (frameEquivOfIsom hf v).vec i = f (v.vec i) := rfl

@[simp] theorem frameEquivOfIsom_symm_vec {oV : Orientation ℝ V (Fin 3)}
    {oW : Orientation ℝ W (Fin 3)} {f : V ≃ₗᵢ[ℝ] W} (hf : IsOrientationPreserving oV oW f)
    (w : FramePlusOf oW) (i : Fin 3) :
    ((frameEquivOfIsom hf).symm w).vec i = f.symm (w.vec i) := rfl

/-- **DERIVED (item 72), principal.**  Reverse reconstruction, uniqueness part: an
orientation-preserving isometry onto the model is determined by the image of a single
oriented orthonormal frame. -/
theorem isom_unique_of_frame_image {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o)
    {f g : V ≃ₗᵢ[ℝ] Model} (h : ∀ i, f (v.vec i) = g (v.vec i)) : f = g :=
  isom_ext_of_frame v h

/-- **DERIVED (items 71–73), principal.**  Reverse reconstruction, existence part: given an
oriented frame of `(V, o)` and an oriented frame of the model, there is exactly one linear
isometry carrying the first to the second, and it is automatically orientation preserving. -/
theorem existsUnique_isom_of_frames {o : Orientation ℝ V (Fin 3)} (v : FramePlusOf o)
    (w : FramePlusOf modelOrient) :
    ∃! f : V ≃ₗᵢ[ℝ] Model,
      IsOrientationPreserving o modelOrient f ∧ ∀ i, f (v.vec i) = w.vec i := by
  refine ⟨(frameChart v).trans (frameChart w).symm, ⟨?_, ?_⟩, ?_⟩
  · exact (frameChart_orientation v).trans (frameChart_orientation w).symm
  · intro i
    show (frameChart w).symm (frameChart v (v.vec i)) = w.vec i
    rw [frameChart_vec, modelFrame_vec, frameChart_symm_single]
  · rintro f ⟨-, hf⟩
    refine isom_ext_of_frame v fun i => ?_
    rw [hf i]
    show w.vec i = (frameChart w).symm (frameChart v (v.vec i))
    rw [frameChart_vec, modelFrame_vec, frameChart_symm_single]

/-- **DERIVED (item 74), principal.**  At a single metric-oriented three-dimensional space
the two notions coincide exactly: orientation-preserving identifications with the model are
in bijection with oriented orthonormal frames. -/
def isomEquivFrame (o : Orientation ℝ V (Fin 3)) :
    {f : V ≃ₗᵢ[ℝ] Model // IsOrientationPreserving o modelOrient f} ≃ FramePlusOf o where
  toFun f := (frameEquivOfIsom f.2).symm modelFrame
  invFun v := ⟨frameChart v, frameChart_orientation v⟩
  left_inv f := by
    refine Subtype.ext (isom_ext_of_frame ((frameEquivOfIsom f.2).symm modelFrame) fun i => ?_)
    rw [frameChart_vec]
    show modelFrame.vec i = (f : V ≃ₗᵢ[ℝ] Model) ((f : V ≃ₗᵢ[ℝ] Model).symm (modelFrame.vec i))
    simp
  right_inv v := by
    refine FramePlusOf.ext fun i => ?_
    show (frameChart v).symm (modelFrame.vec i) = v.vec i
    rw [modelFrame_vec, frameChart_symm_single]

end OneSpace

/-! ## Family-level statements -/

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

@[ext] theorem LocalFibreTriv.ext {F : MetricOrientedRankThreeFamily B E} {U : Set B}
    {Φ Ψ : F.LocalFibreTriv U} (h : ∀ b, Φ.iso b = Ψ.iso b) : Φ = Ψ := by
  cases Φ; cases Ψ; congr 1; exact funext h

/-- **NEWLY DEFINED (item 65), principal.**  The local frame trivialization at a point of `U`
induced by a local fibre trivialization. -/
noncomputable def frameTrivAt {F : MetricOrientedRankThreeFamily B E} {U : Set B}
    (Φ : F.LocalFibreTriv U) (b : U) : F.FramePlusAt (b : B) ≃ FramePlusOf modelOrient :=
  frameEquivOfIsom (Φ.orientation_preserving b)

/-- **DERIVED (items 67–68), principal.**  The induced *local frame trivialization*: over `U`
the total ordinary-frame carrier is equivalent to the product of `U` with the frame carrier of
the model.  This is a set equivalence; no topology is claimed. -/
noncomputable def frameTrivTotal {F : MetricOrientedRankThreeFamily B E} {U : Set B}
    (Φ : F.LocalFibreTriv U) :
    {x : F.FrameTotal // F.frameBase x ∈ U} ≃ U × FramePlusOf modelOrient where
  toFun x := (⟨x.1.1, x.2⟩, frameTrivAt Φ ⟨x.1.1, x.2⟩ x.1.2)
  invFun p := ⟨⟨(p.1 : B), (frameTrivAt Φ p.1).symm p.2⟩, p.1.2⟩
  left_inv := by
    rintro ⟨⟨b, v⟩, hb⟩
    simp
  right_inv := by
    rintro ⟨⟨b, hb⟩, w⟩
    simp

theorem frameTrivTotal_base {F : MetricOrientedRankThreeFamily B E} {U : Set B}
    (Φ : F.LocalFibreTriv U) (x : {x : F.FrameTotal // F.frameBase x ∈ U}) :
    ((frameTrivTotal Φ x).1 : B) = F.frameBase x.1 := rfl

/-- **DERIVED (items 70–74), principal.**  The exact reverse-reconstruction verdict at the
Level-1 (algebraic) level: a local metric-oriented *fibre* trivialization over `U` is the
same thing as a local *frame section* over `U`, i.e. a choice of one oriented orthonormal
frame in each fibre over `U`.  Both directions are constructed, and they are mutually
inverse. -/
noncomputable def fibreTrivEquivFrameSection (F : MetricOrientedRankThreeFamily B E)
    (U : Set B) : F.LocalFibreTriv U ≃ ∀ b : U, F.FramePlusAt (b : B) where
  toFun Φ b := isomEquivFrame (F.orient (b : B)) ⟨Φ.iso b, Φ.orientation_preserving b⟩
  invFun s := F.localFibreTrivOfFrames U s
  left_inv Φ := by
    refine LocalFibreTriv.ext fun b => ?_
    exact congrArg Subtype.val
      ((isomEquivFrame (F.orient (b : B))).symm_apply_apply
        ⟨Φ.iso b, Φ.orientation_preserving b⟩)
  right_inv s := by
    funext b
    exact (isomEquivFrame (F.orient (b : B))).apply_symm_apply (s b)

end MetricOrientedRankThreeFamily

end NullSectorTask26
