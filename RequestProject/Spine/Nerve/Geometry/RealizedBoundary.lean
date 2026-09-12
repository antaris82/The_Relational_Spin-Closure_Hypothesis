import RequestProject.Spine.Nerve.Geometry.PointModel

/-!
# Task 16, consequences: the realized boundary, and the skeletal inclusions

This module records what follows from the Task-16 point model
(`RequestProject/Spine/Nerve/Task16PointModel.lean`):

* **WP5/WP10.** `SpineTask16.range_bdCoord` : the image of `|∂Δ[r]| → |Δ[r]|` is, in the
  barycentric coordinates of the *existing* realization, exactly the set of points having at
  least one vanishing coordinate; equivalently (`realized_boundary_eq_iUnion_faces`) the union
  of the `r+1` coordinate faces.  The complement is the relative interior
  (`compl_range_bdCoord`).
* **WP8.** `SpineTask16.realization_skInc_injective` : the Task-15 reduction is *consumed*.
  Skeletal realization injectivity `|K^{(r-1)}| → |K^{(r)}|` now holds unconditionally, for
  every simplicial set and every `r`.  The *comparison-level* consequences of this (the
  Task-14 one-skeleton step without the hypothesis `B2`, the skeletal induction and the
  finite-dimensional comparison theorem) are not geometry and live one layer up, in
  `RequestProject.Spine.Nerve.Comparison.SkeletalInduction`.
* **WP11.** the dimension-sensitive smoke tests `r = 0` and `r = 1`.

Nothing here reproves skeletal injectivity: `realization_skInc_injective` is a literal
application of `SpineTask15.realization_skInc_injective`.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Finset

universe u

namespace SpineTask16

/-! ## WP5 : the image of the realized boundary -/

/-- The barycentric coordinates of a point in the image of `|∂Δ[r]| → |Δ[r]|` have at least
one vanishing entry, and conversely. -/
theorem range_bdCoord (r : ℕ) :
    Set.range (bdCoord.{u} r) = {u : stdSimplex ℝ (Fin (r + 1)) | ∃ i, u i = 0} := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨k, e, hns, v, -, -, rfl⟩ := normalForm r x
    obtain ⟨i, hi⟩ : ∃ i, ∀ a, e.toOrderHom a ≠ i := by
      by_contra hc
      exact hns (by simpa using hc)
    refine ⟨i, ?_⟩
    rw [bdCoord_faceMap, map_apply]
    exact Finset.sum_eq_zero fun a ha => absurd (Finset.mem_filter.1 ha).2 (hi a)
  · rintro ⟨i, hi⟩
    obtain ⟨k, hk⟩ : ∃ k, (supp u).card = k + 1 :=
      ⟨(supp u).card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 (supp_nonempty u))).symm⟩
    set eemb := (supp u).orderEmbOfFin hk with heemb
    set ehom : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌ := SimplexCategory.Hom.mk ⟨eemb, eemb.monotone⟩
      with hehom
    have hsub : supp u ⊆ Finset.univ.image eemb := by rw [Finset.image_orderEmbOfFin_univ]
    have hns : ¬ Function.Surjective ehom.toOrderHom := by
      intro hsurj
      obtain ⟨a, ha⟩ := hsurj i
      have : i ∈ supp u := ha ▸ Finset.orderEmbOfFin_mem _ hk a
      exact absurd hi (mem_supp.1 this).ne'
    refine ⟨Rz.map (faceMap ehom hns) ((coord ⦋k⦌).symm (restrict eemb eemb.injective u hsub)), ?_⟩
    rw [bdCoord_faceMap]
    exact map_restrict _ _ _ _

/-- The realized boundary is the union of the `r+1` coordinate faces. -/
theorem realized_boundary_eq_iUnion_faces (r : ℕ) :
    Set.range (bdCoord.{u} r)
      = ⋃ i : Fin (r + 1), {u : stdSimplex ℝ (Fin (r + 1)) | u i = 0} := by
  rw [range_bdCoord]
  ext u
  simp

/-- The complement of the realized boundary in `|Δ[r]|` is the relative interior. -/
theorem compl_range_bdCoord (r : ℕ) :
    (Set.range (bdCoord.{u} r))ᶜ = {u : stdSimplex ℝ (Fin (r + 1)) | ∀ i, 0 < u i} := by
  rw [range_bdCoord]
  ext u
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists]
  exact ⟨fun h i => (stdSimplex.zero_le u i).lt_of_ne (Ne.symm (h i)),
    fun h i hi => absurd hi (h i).ne'⟩

/-- The same statement about the underlying map of spaces: the image of `|∂Δ[r]| → |Δ[r]|`
consists exactly of the points of `|Δ[r]|` lying on at least one proper face. -/
theorem range_realization_boundary (r : ℕ) :
    Set.range (Rz.{u}.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι)
      = {x | ∃ i, (coord ⦋r⦌ x) i = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have : coord ⦋r⦌ (Rz.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι y) ∈ Set.range (bdCoord r) :=
      ⟨y, rfl⟩
    rwa [range_bdCoord] at this
  · rintro ⟨i, hi⟩
    have : coord ⦋r⦌ x ∈ Set.range (bdCoord.{u} r) := by rw [range_bdCoord]; exact ⟨i, hi⟩
    obtain ⟨y, hy⟩ := this
    exact ⟨y, (coord ⦋r⦌).injective hy⟩

/-! ## WP8 : the Task-15 reduction, consumed -/

/-- **WP8.**  The realization of the skeletal inclusion is injective, unconditionally, for
every simplicial set and every `r`.  This is the Task-15 reduction
`SpineTask15.realization_skInc_injective` fed with `standardCellMono`. -/
theorem realization_skInc_injective (K : SSet.{u}) (r : ℕ) :
    Function.Injective (Rz.map (SpineTask13.skInc K r)) :=
  SpineTask15.realization_skInc_injective K r (standardCellMono r)

/-! ## WP11 : dimension-sensitive smoke tests -/

/-- `r = 0` : the realization of `∂Δ[0]` is empty. -/
theorem boundaryZero_realization_isEmpty :
    IsEmpty (Rz.{u}.obj (((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex)) : SSet.{u})) :=
  Function.isEmpty
    ((IsInitial.isInitialObj Rz.{u} _ SpineTask15.boundaryZero_isInitial).to (PEmpty.{u + 1}))

/-- `r = 1` : every point of `|∂Δ[1]|` is one of the two vertices of `|Δ[1]|`. -/
theorem boundaryOne_eq_vertex
    (x : Rz.{u}.obj (((∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u})) :
    ∃ i : Fin 2, bdCoord 1 x = stdSimplex.vertex i := by
  obtain ⟨k, e, hns, v, hmono, hpos, rfl⟩ := normalForm 1 x
  -- a strictly monotone non-surjective map into `Fin 2` has a one-point domain
  have hss : Finset.image e.toOrderHom Finset.univ ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.2 fun hall => hns fun i => ?_
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hall ▸ Finset.mem_univ i)
    exact ⟨a, ha⟩
  have hcard := Finset.card_lt_card hss
  rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin] at hcard
  simp only [SimplexCategory.len_mk] at hcard
  obtain rfl : k = 0 := by omega
  refine ⟨e.toOrderHom 0, ?_⟩
  have hv : v = stdSimplex.vertex (0 : Fin (0 + 1)) := by
    ext i
    have hsum : ∑ j, v j = 1 := stdSimplex.sum_eq_one v
    rw [Fin.sum_univ_one] at hsum
    rw [Fin.fin_one_eq_zero i, hsum]
    simp
  rw [bdCoord_faceMap, hv, stdSimplex.map_vertex]

end SpineTask16
