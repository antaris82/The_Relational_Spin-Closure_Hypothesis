import Mathlib.CategoryTheory.Limits.Types.Pushouts
import RequestProject.Spine.Nerve.Geometry.PointModel

/-!
# Task 22, §7 : the geometric separation statement for the attached cell family

This module proves, for the *realized* skeletal attachment square of Task 15, that

```
|Sk X (r+1)|  =  |Sk X r|  ⊔  (the open cells)
```

set-theoretically, i.e.

* `range_skInc_union_range_cellMap` — the images of `|Sk X r|` and of `∐_σ |Δ[r]|` cover
  `|Sk X (r+1)|`;
* `real_cellMap_eq_skInc_iff` — a point of `∐_σ |Δ[r]|` has the same image as a point of
  `|Sk X r|` **iff** it comes from `∐_σ |∂Δ[r]|`;
* `real_cellMap_eq_cellMap_iff` — two points of `∐_σ |Δ[r]|` have the same image **iff** they
  are equal or both lie on `∐_σ |∂Δ[r]|` with the same attaching image.  In particular
  `real_cellMap_injOn_compl_bdry`: distinct **open** cell points stay distinct, so the open
  cells of distinct `σ` are pairwise disjoint and disjoint from the old skeleton.

Everything is derived from the *existing* Task-15 pushout `skeletalIsPushout` (transported to
`Type` by the colimit-preserving functor `SpineTask15.Real`) together with the *existing*
unconditional Task-16 realization monomorphism `SpineTask16.standardCellMono`.  No local
finiteness, no closure-finiteness and no CW theory is used, and the statement is *purely
set-theoretic*: it is the separation input of Task 22 §7 and nothing more.

It is **not** by itself enough for the singular finite-family decomposition (WP3), which needs
in addition an excisive open neighbourhood of the old skeleton; see `TASK22_AUDIT.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet SpineTask13 SpineTask15

universe u

namespace SpineTask22

section Separation

variable (X : SSet.{u}) (r : ℕ)

/-- The Task-15 skeletal attachment square, transported to `Type` (the underlying-set level of
geometric realization). -/
theorem realIsPushout :
    IsPushout (Real.map (attachMap X r)) (Real.map (bdryMap X r))
      (Real.map (skInc X r)) (Real.map (cellMap X r)) :=
  (skeletalIsPushout X r).map Real

/-- The realized boundary inclusion of the cell family is injective (Task 16). -/
theorem real_bdryMap_injective : Function.Injective (Real.map (bdryMap X r)) :=
  Real_sigmaMap_injective _ fun _ => SpineTask16.standardCellMono.{u} r

/-- The explicit set-level model of `|Sk X (r+1)|` as the pushout of
`∐_σ |∂Δ[r]| → ∐_σ |Δ[r]|` along the attaching map. -/
def cellPushoutIso :
    Real.obj (Sk X (r + 1))
      ≅ Types.Pushout (Real.map (bdryMap X r)) (Real.map (attachMap X r)) :=
  IsColimit.coconePointUniqueUpToIso (realIsPushout X r).flip.isColimit
    (Types.Pushout.isColimitCocone _ _)

theorem cellPushoutIso_cellMap (y : Real.obj (attachTgt X r)) :
    (cellPushoutIso X r).hom (Real.map (cellMap X r) y)
      = Types.Pushout.inl (Real.map (bdryMap X r)) (Real.map (attachMap X r)) y :=
  congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom (realIsPushout X r).flip.isColimit
    (Types.Pushout.isColimitCocone _ _) WalkingSpan.left) y

theorem cellPushoutIso_skInc (x : Real.obj (Sk X r)) :
    (cellPushoutIso X r).hom (Real.map (skInc X r) x)
      = Types.Pushout.inr (Real.map (bdryMap X r)) (Real.map (attachMap X r)) x :=
  congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom (realIsPushout X r).flip.isColimit
    (Types.Pushout.isColimitCocone _ _) WalkingSpan.right) x

theorem cellPushoutIso_injective : Function.Injective (cellPushoutIso X r).hom := fun a b h => by
  have := congrArg (cellPushoutIso X r).inv h
  simpa using this

/-- **Joint surjectivity.**  Every point of `|Sk X (r+1)|` lies either in the old skeleton or on
one of the attached cells. -/
theorem range_skInc_union_range_cellMap :
    Set.range (Real.map (skInc X r)) ∪ Set.range (Real.map (cellMap X r)) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨w, hw⟩ : ∃ w, (cellPushoutIso X r).inv w = z :=
    ⟨(cellPushoutIso X r).hom z, congrFun (cellPushoutIso X r).hom_inv_id z⟩
  obtain ⟨y | x⟩ := w
  · refine Or.inr ⟨y, cellPushoutIso_injective X r ?_⟩
    rw [cellPushoutIso_cellMap, ← hw]
    exact (congrFun (cellPushoutIso X r).inv_hom_id _).symm
  · refine Or.inl ⟨x, cellPushoutIso_injective X r ?_⟩
    rw [cellPushoutIso_skInc, ← hw]
    exact (congrFun (cellPushoutIso X r).inv_hom_id _).symm

/-- **Separation, cell against old skeleton.**  A point of the cell family and a point of the
old skeleton have the same image in `|Sk X (r+1)|` exactly when they both come from the
boundary of the cell family. -/
theorem real_cellMap_eq_skInc_iff (y : Real.obj (attachTgt X r)) (x : Real.obj (Sk X r)) :
    Real.map (cellMap X r) y = Real.map (skInc X r) x
      ↔ ∃ w, Real.map (bdryMap X r) w = y ∧ Real.map (attachMap X r) w = x := by
  haveI : Mono (Real.map (bdryMap X r)) :=
    (mono_iff_injective _).2 (real_bdryMap_injective X r)
  constructor
  · intro h
    have h' : Types.Pushout.inl (Real.map (bdryMap X r)) (Real.map (attachMap X r)) y
        = Types.Pushout.inr (Real.map (bdryMap X r)) (Real.map (attachMap X r)) x := by
      rw [← cellPushoutIso_cellMap, ← cellPushoutIso_skInc, h]
    exact (Types.Pushout.inl_eq_inr_iff _ _ y x).1 h'
  · rintro ⟨w, rfl, rfl⟩
    exact congrFun (realIsPushout X r).flip.w w

/-- **Separation, cell against cell.**  Two points of the cell family have the same image in
`|Sk X (r+1)|` exactly when they are equal, or both lie on the boundary and are attached to the
same point of the old skeleton. -/
theorem real_cellMap_eq_cellMap_iff (y y' : Real.obj (attachTgt X r)) :
    Real.map (cellMap X r) y = Real.map (cellMap X r) y'
      ↔ y = y' ∨ ∃ w w', Real.map (attachMap X r) w = Real.map (attachMap X r) w'
          ∧ y = Real.map (bdryMap X r) w ∧ y' = Real.map (bdryMap X r) w' := by
  haveI : Mono (Real.map (bdryMap X r)) :=
    (mono_iff_injective _).2 (real_bdryMap_injective X r)
  constructor
  · intro h
    have h' : (Quot.mk _ (Sum.inl y)
        : Types.Pushout (Real.map (bdryMap X r)) (Real.map (attachMap X r)))
        = Quot.mk _ (Sum.inl y') := by
      rw [show (Quot.mk _ (Sum.inl y)
          : Types.Pushout (Real.map (bdryMap X r)) (Real.map (attachMap X r)))
          = (cellPushoutIso X r).hom (Real.map (cellMap X r) y) from
        (cellPushoutIso_cellMap X r y).symm,
        show (Quot.mk _ (Sum.inl y')
          : Types.Pushout (Real.map (bdryMap X r)) (Real.map (attachMap X r)))
          = (cellPushoutIso X r).hom (Real.map (cellMap X r) y') from
        (cellPushoutIso_cellMap X r y').symm, h]
    have h'' := (Types.Pushout.quot_mk_eq_iff _ _ (Sum.inl y) (Sum.inl y')).1 h'
    rw [Types.Pushout.inl_rel'_inl_iff] at h''
    rcases h'' with h1 | ⟨x₀, y₀, hxy, h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨x₀, y₀, hxy, h1, h2⟩
  · rintro (rfl | ⟨w, w', hww', rfl, rfl⟩)
    · rfl
    · have hw : Real.map (cellMap X r) (Real.map (bdryMap X r) w)
          = Real.map (skInc X r) (Real.map (attachMap X r) w) :=
        congrFun (realIsPushout X r).flip.w w
      have hw' : Real.map (cellMap X r) (Real.map (bdryMap X r) w')
          = Real.map (skInc X r) (Real.map (attachMap X r) w') :=
        congrFun (realIsPushout X r).flip.w w'
      show Real.map (cellMap X r) (Real.map (bdryMap X r) w)
        = Real.map (cellMap X r) (Real.map (bdryMap X r) w')
      rw [hw, hw', hww']

/-- **The open cells are pairwise disjoint.**  Off the boundary the total characteristic map of
the cell family is injective. -/
theorem real_cellMap_injOn_compl_bdry {y y' : Real.obj (attachTgt X r)}
    (hy : y ∉ Set.range (Real.map (bdryMap X r)))
    (h : Real.map (cellMap X r) y = Real.map (cellMap X r) y') : y = y' := by
  rcases (real_cellMap_eq_cellMap_iff X r y y').1 h with h1 | ⟨w, _, _, hyw, _⟩
  · exact h1
  · exact absurd ⟨w, hyw.symm⟩ hy

/-- **The open cells miss the old skeleton.** -/
theorem real_cellMap_notMem_range_skInc {y : Real.obj (attachTgt X r)}
    (hy : y ∉ Set.range (Real.map (bdryMap X r))) :
    Real.map (cellMap X r) y ∉ Set.range (Real.map (skInc X r)) := by
  rintro ⟨x, hx⟩
  obtain ⟨w, hw, -⟩ := (real_cellMap_eq_skInc_iff X r y x).1 hx.symm
  exact hy ⟨w, hw⟩

/-- **§7, the required geometric separation statement.**  The complement of the old skeleton in
`|Sk X (r+1)|` is exactly the image of the complement of `∐_σ |∂Δ[r]|` in `∐_σ |Δ[r]|`, and the
total characteristic map is injective there. -/
theorem compl_range_skInc :
    (Set.range (Real.map (skInc X r)))ᶜ
      = Real.map (cellMap X r) '' (Set.range (Real.map (bdryMap X r)))ᶜ := by
  ext z
  constructor
  · intro hz
    have hcov := range_skInc_union_range_cellMap X r
    have : z ∈ Set.range (Real.map (skInc X r)) ∪ Set.range (Real.map (cellMap X r)) := by
      rw [hcov]; trivial
    rcases this with h | ⟨y, rfl⟩
    · exact absurd h hz
    · refine ⟨y, ?_, rfl⟩
      intro hy
      obtain ⟨w, hw⟩ := hy
      refine hz ⟨Real.map (attachMap X r) w, ?_⟩
      rw [← hw]
      exact (congrFun (realIsPushout X r).flip.w w).symm
  · rintro ⟨y, hy, rfl⟩
    exact real_cellMap_notMem_range_skInc X r hy

end Separation

end SpineTask22
