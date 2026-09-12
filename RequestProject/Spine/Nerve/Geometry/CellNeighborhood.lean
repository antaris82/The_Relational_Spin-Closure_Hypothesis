import Mathlib.CategoryTheory.Limits.Types.Pushouts
import RequestProject.Spine.Nerve.Geometry.PuncturedSimplex

/-!
# Task 23, WP1 — open/closed-set control in the realized skeletal pushout

This module proves the point-set facts that the excision step of Task 23 needs, using the
*existing* Task-15 realized pushout

```
∐_{σ ∈ NDeg_r} |∂Δ[r]| ──────▶ |Sk X r|
        │                          │
        ▼                          ▼
∐_{σ ∈ NDeg_r}  |Δ[r]| ──────▶ |Sk X (r+1)|
```

(`SpineTask15.skeletalIsPushout_toTop_coprod`) together with the pinned Mathlib colimit
topology API `TopCat.isOpen_iff_of_isColimit` / `TopCat.isClosed_iff_of_isColimit`.  **These
theorems do exist at the production pin**; the Task-22 audit statement to the contrary is
corrected in `TASK23_AUDIT.md`.

Contents.

* a small toolkit for points of a `TopCat` coproduct (`exists_ι`, `ι_eq_component`,
  `ι_injective`, `isClosed_coprod_iff`);
* `isClosed_iff_of_isPushout`, `isOpen_iff_of_isPushout`: a subset of the pushout is
  closed/open iff both its preimages are;
* `isClosed_range_skInc`: **the old realized skeleton `A = |Sk X r|` is closed in
  `Y = |Sk X (r+1)|`**;
* `baryPoint_notMem_range_skInc`: **the barycentre of every newly attached cell lies off
  `A`**;
* `isClosed_barySet`: **the set `B` of the barycentres of the new cells is closed in `Y`**
  (no finiteness of the cell family is needed for this);
* `isOpen_puncturedNbhd` : `V = Y \ B` is open, `isOpen_openCells` : `U = Y \ A` is open, and
  `openCells_union_puncturedNbhd` : `U ∪ V = Y`.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask15 SpineTask17

universe u

namespace SpineTask23

/-! ## Points of a coproduct of topological spaces -/

section Coprod

variable {J : Type u}

theorem exists_ι (A : J → TopCat.{u}) (z : ↥(∐ A)) :
    ∃ (j : J) (a : A j), (Limits.Sigma.ι A j) a = z := by
  set w := (TopCat.sigmaIsoSigma A).hom z with hw
  refine ⟨w.1, w.2, ?_⟩
  calc (Limits.Sigma.ι A w.1) w.2 = (TopCat.sigmaIsoSigma A).inv ⟨w.1, w.2⟩ :=
        (TopCat.sigmaIsoSigma_inv_apply A w.1 w.2).symm
    _ = z := ConcreteCategory.congr_hom (TopCat.sigmaIsoSigma A).hom_inv_id z

theorem ι_eq_component (A : J → TopCat.{u}) {j k : J} {a : A j} {b : A k}
    (h : (Limits.Sigma.ι A j) a = (Limits.Sigma.ι A k) b) : j = k := by
  have h1 := congrArg (TopCat.sigmaIsoSigma A).hom h
  rw [TopCat.sigmaIsoSigma_hom_ι_apply, TopCat.sigmaIsoSigma_hom_ι_apply] at h1
  exact congrArg Sigma.fst h1

theorem ι_injective (A : J → TopCat.{u}) (j : J) :
    Function.Injective (Limits.Sigma.ι A j) := by
  intro a b h
  have h1 := congrArg (TopCat.sigmaIsoSigma A).hom h
  rw [TopCat.sigmaIsoSigma_hom_ι_apply, TopCat.sigmaIsoSigma_hom_ι_apply] at h1
  simpa using h1

theorem isClosed_coprod_iff (A : J → TopCat.{u}) (S : Set ↥(∐ A)) :
    IsClosed S ↔ ∀ j, IsClosed (Limits.Sigma.ι A j ⁻¹' S) := by
  rw [TopCat.isClosed_iff_of_isColimit _ (colimit.isColimit (Discrete.functor A)) S]
  exact ⟨fun h j => h ⟨j⟩, fun h j => by cases j; exact h _⟩

theorem sigmaMap_apply {A B : J → TopCat.{u}} (p : ∀ j, A j ⟶ B j) (j : J) (a : A j) :
    (Limits.Sigma.map p) ((Limits.Sigma.ι A j) a) = (Limits.Sigma.ι B j) (p j a) :=
  ConcreteCategory.congr_hom (Limits.Sigma.ι_map p j) a

theorem sigmaMap_injective {A B : J → TopCat.{u}} (p : ∀ j, A j ⟶ B j)
    (hp : ∀ j, Function.Injective (p j)) : Function.Injective (Limits.Sigma.map p) := by
  intro z z' h
  obtain ⟨j, a, rfl⟩ := exists_ι A z
  obtain ⟨k, b, rfl⟩ := exists_ι A z'
  rw [sigmaMap_apply, sigmaMap_apply] at h
  obtain rfl : j = k := ι_eq_component B h
  exact congrArg _ (hp _ (ι_injective B _ h))

theorem preimage_ι_range_sigmaMap {A B : J → TopCat.{u}} (p : ∀ j, A j ⟶ B j) (j : J) :
    (Limits.Sigma.ι B j) ⁻¹' (Set.range (Limits.Sigma.map p)) = Set.range (p j) := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨k, a, rfl⟩ := exists_ι A z
    rw [sigmaMap_apply] at hz
    obtain rfl : k = j := ι_eq_component B hz
    exact ⟨a, ι_injective B _ hz⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(Limits.Sigma.ι A j) a, sigmaMap_apply p j a⟩

theorem isClosed_range_sigmaMap {A B : J → TopCat.{u}} (p : ∀ j, A j ⟶ B j)
    (hp : ∀ j, IsClosed (Set.range (p j))) : IsClosed (Set.range (Limits.Sigma.map p)) := by
  rw [isClosed_coprod_iff]
  intro j
  rw [preimage_ι_range_sigmaMap]
  exact hp j

end Coprod

/-! ## Open and closed subsets of a pushout -/

section PushoutSets

theorem isClosed_iff_of_isPushout {W A B Y : TopCat.{u}} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) (S : Set Y) :
    IsClosed S ↔ IsClosed (i ⁻¹' S) ∧ IsClosed (j ⁻¹' S) := by
  rw [TopCat.isClosed_iff_of_isColimit _ h.isColimit S]
  constructor
  · intro H
    exact ⟨H WalkingSpan.left, H WalkingSpan.right⟩
  · rintro ⟨h1, h2⟩ (_ | jj)
    · have hz : (h.cocone.ι.app WalkingSpan.zero) ⁻¹' S = f ⁻¹' (i ⁻¹' S) := by
        rw [← Set.preimage_comp]; congr 1
      rw [hz]
      exact h1.preimage f.hom.continuous
    · cases jj <;> [exact h1; exact h2]

theorem isOpen_iff_of_isPushout {W A B Y : TopCat.{u}} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) (S : Set Y) :
    IsOpen S ↔ IsOpen (i ⁻¹' S) ∧ IsOpen (j ⁻¹' S) := by
  simp only [← isClosed_compl_iff, ← Set.preimage_compl]
  exact isClosed_iff_of_isPushout h Sᶜ

/-- Two points of the two legs of a pushout **of types** have the same image exactly when they
come from a common point of the apex — provided the left leg of the span is injective. -/
theorem inl_eq_inr_iff_of_isPushout {W A B Y : Type u} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) (hf : Function.Injective f) (a : A) (b : B) :
    i a = j b ↔ ∃ w, f w = a ∧ g w = b := by
  haveI : Mono f := (mono_iff_injective _).2 hf
  let e : Y ≅ Types.Pushout f g :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (Types.Pushout.isColimitCocone _ _)
  have hi : ∀ a, e.hom (i a) = Types.Pushout.inl f g a :=
    fun a => congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit
      (Types.Pushout.isColimitCocone _ _) WalkingSpan.left) a
  have hj : ∀ b, e.hom (j b) = Types.Pushout.inr f g b :=
    fun b => congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit
      (Types.Pushout.isColimitCocone _ _) WalkingSpan.right) b
  constructor
  · intro hab
    have hh : Types.Pushout.inl f g a = Types.Pushout.inr f g b := by rw [← hi, ← hj, hab]
    exact (Types.Pushout.inl_eq_inr_iff _ _ a b).1 hh
  · rintro ⟨w, rfl, rfl⟩
    exact congrFun h.w w

/-- Two points of the *left* leg of a pushout of types have the same image exactly when they
are equal, or both come from the apex with the same image on the right. -/
theorem inl_eq_inl_iff_of_isPushout {W A B Y : Type u} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) (hf : Function.Injective f) (a a' : A) :
    i a = i a' ↔ a = a' ∨ ∃ w w', g w = g w' ∧ a = f w ∧ a' = f w' := by
  haveI : Mono f := (mono_iff_injective _).2 hf
  let e : Y ≅ Types.Pushout f g :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (Types.Pushout.isColimitCocone _ _)
  have hi : ∀ a, e.hom (i a) = Types.Pushout.inl f g a :=
    fun a => congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit
      (Types.Pushout.isColimitCocone _ _) WalkingSpan.left) a
  constructor
  · intro hab
    have hh : (Quot.mk _ (Sum.inl a) : Types.Pushout f g) = Quot.mk _ (Sum.inl a') := by
      rw [show (Quot.mk _ (Sum.inl a) : Types.Pushout f g) = e.hom (i a) from (hi a).symm,
        show (Quot.mk _ (Sum.inl a') : Types.Pushout f g) = e.hom (i a') from (hi a').symm, hab]
    have h'' := (Types.Pushout.quot_mk_eq_iff _ _ (Sum.inl a) (Sum.inl a')).1 hh
    rw [Types.Pushout.inl_rel'_inl_iff] at h''
    rcases h'' with h1 | ⟨w, w', hww', h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨w, w', hww', h1, h2⟩
  · rintro (rfl | ⟨w, w', hww', rfl, rfl⟩)
    · rfl
    · have h1 : i (f w) = j (g w) := congrFun h.w w
      have h2 : i (f w') = j (g w') := congrFun h.w w'
      rw [h1, h2, hww']

/-- Off the image of the apex, the left leg of a pushout of types is injective. -/
theorem inl_injOn_of_isPushout {W A B Y : Type u} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) (hf : Function.Injective f) {a a' : A}
    (ha : a ∉ Set.range f) (haa : i a = i a') : a = a' := by
  rcases (inl_eq_inl_iff_of_isPushout h hf a a').1 haa with h1 | ⟨w, _, _, hw, _⟩
  · exact h1
  · exact absurd ⟨w, hw.symm⟩ ha

end PushoutSets

/-! ## The realized skeletal attachment, as a pushout of topological spaces -/

section Skeleton

variable (X : SSet.{u}) (r : ℕ)

/-- The Task-15 realized skeletal pushout, in the coproduct form. -/
theorem topIsPushout :
    IsPushout (topAttachMap X r) (topBdryMap X r) (SSet.toTop.map (skInc X r))
      (topCellMap X r) :=
  skeletalIsPushout_toTop_coprod X r

/-- The same square, viewed in `Type`. -/
theorem typeIsPushout :
    IsPushout ((forget TopCat).map (topBdryMap X r)) ((forget TopCat).map (topAttachMap X r))
      ((forget TopCat).map (topCellMap X r))
      ((forget TopCat).map (SSet.toTop.map (skInc X r))) :=
  ((topIsPushout X r).flip).map (forget TopCat.{u})

/-- The realized boundary inclusion of the cell family is injective (Task 16). -/
theorem topBdryMap_injective : Function.Injective (topBdryMap X r) :=
  sigmaMap_injective _ fun _ => SpineTask16.standardCellMono.{u} r

/-- The realized boundary of the cell family is closed in the cell family (Task 17). -/
theorem isClosed_range_topBdryMap : IsClosed (Set.range (topBdryMap X r)) :=
  isClosed_range_sigmaMap _ fun _ =>
    (isClosedEmbedding_realization_boundary.{u} r).isClosed_range

/-- **Separation, cell against old skeleton**, in the coproduct form. -/
theorem topCellMap_eq_skInc_iff (y : ↥(topAttachTgt X r)) (x : ↥(SSet.toTop.obj (Sk X r))) :
    topCellMap X r y = SSet.toTop.map (skInc X r) x
      ↔ ∃ w, topBdryMap X r w = y ∧ topAttachMap X r w = x :=
  inl_eq_inr_iff_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r) y x

/-- The preimage of the old skeleton in the cell family is exactly the boundary of the cell
family. -/
theorem preimage_topCellMap_range_skInc :
    (topCellMap X r) ⁻¹' (Set.range (SSet.toTop.map (skInc X r)))
      = Set.range (topBdryMap X r) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨w, hw, -⟩ := (topCellMap_eq_skInc_iff X r y x).1 hx.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨topAttachMap X r w, ((topCellMap_eq_skInc_iff X r _ _).2 ⟨w, rfl, rfl⟩).symm⟩

/-- **WP1(1).  The old realized skeleton `A = |Sk X r|` is closed in `Y = |Sk X (r+1)|`.** -/
theorem isClosed_range_skInc :
    IsClosed (Set.range (SSet.toTop.map (skInc X r))) := by
  rw [isClosed_iff_of_isPushout (topIsPushout X r)]
  constructor
  · have : (SSet.toTop.map (skInc X r)) ⁻¹' (Set.range (SSet.toTop.map (skInc X r)))
        = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
    rw [this]
    exact isClosed_univ
  · rw [preimage_topCellMap_range_skInc]
    exact isClosed_range_topBdryMap X r

/-! ### The barycentres of the newly attached cells -/

/-- The barycentre of the `σ`-cell, as a point of `∐_σ |Δ[r]|`. -/
def cellBaryPt (σ : X.nonDegenerate r) : ↥(topAttachTgt X r) :=
  (Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ)
    (cellBary.{u} r)

/-- The barycentre of the `σ`-cell, as a point of `|Sk X (r+1)|`. -/
def baryPoint (σ : X.nonDegenerate r) : ↥(SSet.toTop.obj (Sk X (r + 1))) :=
  (topCellMap X r) (cellBaryPt X r σ)

/-- The barycentre of a cell is not on the boundary of the cell family. -/
theorem cellBaryPt_notMem_range_topBdryMap (σ : X.nonDegenerate r) :
    cellBaryPt X r σ ∉ Set.range (topBdryMap X r) := by
  intro hmem
  have h1 : cellBary.{u} r ∈
      (Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) ⁻¹'
        (Set.range (topBdryMap X r)) := hmem
  rw [topBdryMap, preimage_ι_range_sigmaMap] at h1
  obtain ⟨b, hb⟩ := h1
  exact (cellBdryIncl_mem_puncturedCell.{u} r b) hb

/-- **WP1(2).  The barycentre of a newly attached cell lies outside the old skeleton.** -/
theorem baryPoint_notMem_range_skInc (σ : X.nonDegenerate r) :
    baryPoint X r σ ∉ Set.range (SSet.toTop.map (skInc X r)) := by
  intro hmem
  have : cellBaryPt X r σ ∈ (topCellMap X r) ⁻¹' (Set.range (SSet.toTop.map (skInc X r))) := hmem
  rw [preimage_topCellMap_range_skInc] at this
  exact cellBaryPt_notMem_range_topBdryMap X r σ this

/-- **The set `B` of the barycentres of the newly attached cells.** -/
def barySet : Set ↥(SSet.toTop.obj (Sk X (r + 1))) := Set.range (baryPoint X r)

theorem preimage_topCellMap_barySet :
    (topCellMap X r) ⁻¹' (barySet X r) = Set.range (cellBaryPt X r) := by
  ext y
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    exact inl_injOn_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r)
      (cellBaryPt_notMem_range_topBdryMap X r σ) hσ
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, rfl⟩

theorem preimage_ι_range_cellBaryPt (τ : X.nonDegenerate r) :
    (Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) τ) ⁻¹'
        (Set.range (cellBaryPt X r))
      = {cellBary.{u} r} := by
  ext x
  constructor
  · rintro ⟨σ, hσ⟩
    have hσ' : (Limits.Sigma.ι
        (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) (cellBary.{u} r)
        = (Limits.Sigma.ι
          (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) τ) x := hσ
    obtain rfl : σ = τ := ι_eq_component _ hσ'
    exact (ι_injective _ _ hσ').symm
  · rintro rfl
    exact ⟨τ, rfl⟩

/-- **WP1(3).  The barycentre set `B` is closed in `Y`.** -/
theorem isClosed_barySet : IsClosed (barySet X r) := by
  rw [isClosed_iff_of_isPushout (topIsPushout X r)]
  constructor
  · have hempty : (SSet.toTop.map (skInc X r)) ⁻¹' (barySet X r) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨σ, hσ⟩
      exact baryPoint_notMem_range_skInc X r σ ⟨x, hσ.symm⟩
    rw [hempty]
    exact isClosed_empty
  · rw [preimage_topCellMap_barySet, isClosed_coprod_iff]
    intro τ
    rw [preimage_ι_range_cellBaryPt]
    exact isClosed_singleton

/-! ### The two open sets of the excisive family -/

/-- `V = Y \ B`, the complement of the barycentres. -/
def puncturedNbhd : Set ↥(SSet.toTop.obj (Sk X (r + 1))) := (barySet X r)ᶜ

/-- `U = Y \ A`, the union of the open cells. -/
def openCells : Set ↥(SSet.toTop.obj (Sk X (r + 1))) :=
  (Set.range (SSet.toTop.map (skInc X r)))ᶜ

/-- **WP1(4).  `V = Y \ B` is open.** -/
theorem isOpen_puncturedNbhd : IsOpen (puncturedNbhd X r) :=
  (isClosed_barySet X r).isOpen_compl

theorem isOpen_openCells : IsOpen (openCells X r) :=
  (isClosed_range_skInc X r).isOpen_compl

/-- The old skeleton is contained in `V`. -/
theorem range_skInc_subset_puncturedNbhd :
    Set.range (SSet.toTop.map (skInc X r)) ⊆ puncturedNbhd X r := by
  rintro z ⟨x, rfl⟩ ⟨σ, hσ⟩
  exact baryPoint_notMem_range_skInc X r σ ⟨x, hσ.symm⟩

/-- **The excisive cover.**  `U ∪ V = Y`. -/
theorem openCells_union_puncturedNbhd :
    openCells X r ∪ puncturedNbhd X r = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases hz : z ∈ Set.range (SSet.toTop.map (skInc X r))
  · exact Or.inr (range_skInc_subset_puncturedNbhd X r hz)
  · exact Or.inl hz

end Skeleton

end SpineTask23
