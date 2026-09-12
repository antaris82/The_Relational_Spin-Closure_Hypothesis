import RequestProject.Spine.E2.Family.FiberFrames

/-!
# Task 26, Package D: the total ordinary-frame carrier

**Hard target B, second half (items 45–50).**

The total carrier is the plain dependent sum of the fibrewise frame carriers, with its
first projection to the base.  We prove that the fibre of the projection over `b` is exactly
`FramePlusAt b`, and that the projection is surjective, the latter from fibrewise
nonemptiness alone.

**This object is deliberately not called a frame bundle (item 49).**  No topology is attached
to it (item 50): none of the carriers involved (`OrthonormalBasis`-subtypes, and the sigma
type over them) carries a `TopologicalSpace` instance in this development, so no topology is
inherited definitionally either.  The corresponding negative control for the *fibre* sigma
type — where a topology *is* automatically available and is the wrong one — is proved at the
end of this module.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **NEWLY DEFINED (item 45), principal.**  The total carrier of ordinary (positively
oriented orthonormal) frames of the family.  It is a dependent sum, nothing more. -/
def FrameTotal (F : MetricOrientedRankThreeFamily B E) : Type _ :=
  Σ b : B, F.FramePlusAt b

/-- **NEWLY DEFINED (item 46), principal.**  The projection of the total frame carrier to the
base. -/
def frameBase (F : MetricOrientedRankThreeFamily B E) : F.FrameTotal → B := Sigma.fst

@[simp] theorem frameBase_mk (F : MetricOrientedRankThreeFamily B E) (b : B)
    (v : F.FramePlusAt b) : F.frameBase ⟨b, v⟩ = b := rfl

/-- **DERIVED (item 47), principal.**  The fibre of the projection over `b` is exactly
`FramePlusAt b`. -/
def frameFiberEquiv (F : MetricOrientedRankThreeFamily B E) (b : B) :
    {x : F.FrameTotal // F.frameBase x = b} ≃ F.FramePlusAt b where
  toFun x := by
    refine cast ?_ x.1.2
    rw [show x.1.1 = b from x.2]
  invFun v := ⟨⟨b, v⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b', v⟩, rfl⟩
    rfl
  right_inv := by
    intro v
    rfl

@[simp] theorem frameFiberEquiv_symm_apply (F : MetricOrientedRankThreeFamily B E) (b : B)
    (v : F.FramePlusAt b) : (F.frameFiberEquiv b).symm v = ⟨⟨b, v⟩, rfl⟩ := rfl

/-- **DERIVED (item 47).**  The set-level description of the same fact: the preimage of `{b}`
consists exactly of the pairs with first component `b`. -/
theorem frameBase_preimage (F : MetricOrientedRankThreeFamily B E) (b : B) :
    F.frameBase ⁻¹' {b} = {x : F.FrameTotal | x.1 = b} := rfl

/-- **DERIVED (item 48), principal.**  The projection is surjective; this uses exactly the
fibrewise existence of frames and nothing else. -/
theorem frameBase_surjective (F : MetricOrientedRankThreeFamily B E) :
    Function.Surjective F.frameBase := by
  intro b
  obtain ⟨v⟩ := F.framePlusAt_nonempty b
  exact ⟨⟨b, v⟩, rfl⟩

/-- **DERIVED.**  Equality in the total carrier splits into equality of base points and, over
a fixed base point, equality of frames. -/
theorem frameTotal_ext {F : MetricOrientedRankThreeFamily B E} {x y : F.FrameTotal}
    (h : x.1 = y.1) (h2 : HEq x.2 y.2) : x = y :=
  Sigma.ext h h2

end MetricOrientedRankThreeFamily

/-! ## Negative control (item 105): the automatic sigma topology is not a bundle topology -/

section SigmaTopology

variable {B : Type u} {E : B → Type v} [∀ b, TopologicalSpace (E b)]

/-- **NEGATIVE CONTROL (item 105).**  The topology that the dependent sum `Σ b, E b` carries
automatically (the disjoint-union topology of the fibres) makes every fibre an *open* subset.
For a base that is not discrete this is not the topology of a fibre bundle, so the sigma type
must not be silently interpreted as a topological total space. -/
theorem isOpen_sigmaFiber (b : B) : IsOpen {x : Σ b : B, E b | x.1 = b} := by
  rw [isOpen_sigma_iff]
  intro i
  by_cases h : i = b
  · subst h
    simp
  · have : (Sigma.mk i ⁻¹' {x : Σ b : B, E b | x.1 = b}) = ∅ := by
      ext y; simp [h]
    rw [this]
    exact isOpen_empty

end SigmaTopology

end NullSectorTask26
