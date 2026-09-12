import RequestProject.Spine.Nerve.Geometry.CellNeighborhood

/-!
# Task 23, WP3 — descending the cellwise radial deformation through the realized pushout

Let `A = |Sk X r|`, `Y = |Sk X (r+1)|`, let `B` be the set of barycentres of the newly attached
`r`-cells (Task 23 WP1) and let `V = Y \ B`.

This module descends the cellwise radial deformation retraction of Task 23 WP2 through the
Task-15 realized pushout, and produces a **deformation retraction of `V` onto `A`, fixing `A`
pointwise**:

* `skToV`          : the inclusion `A ⟶ V`;
* `vRetract`       : the retraction `V ⟶ A`;
* `vRetract_skToV` : `vRetract ∘ skToV = id`;
* `vHomotopy`      : a homotopy `[0,1] × V ⟶ V`;
* `vHomotopy_zero` : `vHomotopy 0 = id`;
* `vHomotopy_one`  : `vHomotopy 1 = skToV ∘ vRetract`;
* `vHomotopy_fix`  : `vHomotopy t (skToV x) = skToV x` for all `t`.

The descent is *not* an informal pointwise gluing.  It goes through the explicit quotient
presentation

```
q : |Sk X r| ⊕ (Σ_σ (|Δ[r]| \ {b_r}))  ⟶  V,
```

proved to be a **quotient map** (`isQuotientMap_totMap`) from the pinned colimit topology API
(`TopCat.isOpen_iff_of_isColimit`, through `isOpen_iff_of_isPushout` of Task 23 WP1) together
with openness of `V` in `Y` and of the punctured cell in `|Δ[r]|`.  Maps out of `V` are then
obtained by the descent lemmas `descend` and `descendHomotopy`, the latter using the pinned
`Topology.IsQuotientMap.continuous_lift_prod_right` (the interval is locally compact), so joint
continuity of the homotopy is *proved*, not assumed.

No finiteness of the cell family is used in this module.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask15 SpineTask17

universe u

namespace SpineTask23

/-- Two legs of a pushout of types are jointly surjective. -/
theorem jointly_surjective_of_isPushout {W A B Y : Type u} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) (z : Y) : (∃ a, i a = z) ∨ (∃ b, j b = z) := by
  let e : Y ≅ Types.Pushout f g :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (Types.Pushout.isColimitCocone _ _)
  have hi : ∀ a, e.hom (i a) = Types.Pushout.inl f g a :=
    fun a => congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit
      (Types.Pushout.isColimitCocone _ _) WalkingSpan.left) a
  have hj : ∀ b, e.hom (j b) = Types.Pushout.inr f g b :=
    fun b => congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit
      (Types.Pushout.isColimitCocone _ _) WalkingSpan.right) b
  have hinj : Function.Injective e.hom := fun a b hab => by
    have := congrArg e.inv hab
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w, e.inv w = z := ⟨e.hom z, congrFun e.hom_inv_id z⟩
  obtain ⟨a | b⟩ := w
  · refine Or.inl ⟨a, hinj ?_⟩
    rw [hi, ← hw]
    exact (congrFun e.inv_hom_id _).symm
  · refine Or.inr ⟨b, hinj ?_⟩
    rw [hj, ← hw]
    exact (congrFun e.inv_hom_id _).symm

section Descent

variable (X : SSet.{u}) (r : ℕ)

/-! ## The punctured cell family and the quotient presentation of `V` -/

/-- The index-`s` inclusion of a realized cell into the cell family. -/
abbrev cellι (s : X.nonDegenerate r) :
    SSet.toTop.{u}.obj (Δ[r] : SSet.{u}) ⟶ topAttachTgt X r :=
  Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) s

/-- The index-`s` inclusion of a realized cell boundary into the boundary family. -/
abbrev bdryι (s : X.nonDegenerate r) :
    SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶
      topAttachSrc X r :=
  Limits.Sigma.ι (fun _ : X.nonDegenerate r =>
    SSet.toTop.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})) s

theorem topCellMap_cellι (s : X.nonDegenerate r)
    (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    (topCellMap X r) ((cellι X r s) c) = (SSet.toTop.map (cellChar X r s)) c := by
  have h : cellι X r s ≫ topCellMap X r = SSet.toTop.map (cellChar X r s) :=
    Limits.Sigma.ι_desc _ s
  exact ConcreteCategory.congr_hom h c

theorem topAttachMap_bdryι (s : X.nonDegenerate r)
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    (topAttachMap X r) ((bdryι X r s) b) = (SSet.toTop.map (cellAttach X r s)) b := by
  have h : bdryι X r s ≫ topAttachMap X r = SSet.toTop.map (cellAttach X r s) :=
    Limits.Sigma.ι_desc _ s
  exact ConcreteCategory.congr_hom h b

theorem topBdryMap_bdryι (s : X.nonDegenerate r)
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    (topBdryMap X r) ((bdryι X r s) b)
      = (cellι X r s) ((SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) b) :=
  sigmaMap_apply (fun _ : X.nonDegenerate r =>
    SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) s b

/-- The realized characteristic map of the `s`-cell agrees, on the boundary, with the skeletal
inclusion of the attaching map. -/
theorem cellChar_bdry (s : X.nonDegenerate r)
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    (SSet.toTop.map (cellChar X r s))
        ((SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) b)
      = (SSet.toTop.map (skInc X r)) ((SSet.toTop.map (cellAttach X r s)) b) := by
  have h := congrArg (fun f : ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
    Sk X (r + 1) => SSet.toTop.map f) (cellAttach_comm X r s)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h.symm b

theorem cellBaryPt_eq (s : X.nonDegenerate r) :
    cellBaryPt X r s = (cellι X r s) (cellBary.{u} r) := rfl

theorem topCellMap_mem_puncturedNbhd (s : X.nonDegenerate r) (c : ↥(puncturedCell.{u} r)) :
    (topCellMap X r) ((cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))))
      ∈ puncturedNbhd X r := by
  rintro ⟨t, ht⟩
  have ht' : (topCellMap X r) (cellBaryPt X r t)
      = (topCellMap X r) ((cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) := ht
  have heq := inl_injOn_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r)
    (cellBaryPt_notMem_range_topBdryMap X r t) ht'
  rw [cellBaryPt_eq] at heq
  obtain rfl : t = s := ι_eq_component _ heq
  exact c.2 (ι_injective _ _ heq).symm

theorem skInc_mem_puncturedNbhd (x : ↥(SSet.toTop.{u}.obj (Sk X r))) :
    (SSet.toTop.map (skInc X r)) x ∈ puncturedNbhd X r :=
  range_skInc_subset_puncturedNbhd X r ⟨x, rfl⟩

/-- The total space of the quotient presentation of `V`: the old skeleton together with the
family of punctured cells. -/
abbrev Tot : Type u :=
  ↥(SSet.toTop.{u}.obj (Sk X r)) ⊕ (Σ _ : X.nonDegenerate r, ↥(puncturedCell.{u} r))

/-- The quotient presentation of `V = Y \ B`. -/
def totMap : Tot X r → ↥(puncturedNbhd X r) :=
  Sum.elim
    (fun x => ⟨(SSet.toTop.map (skInc X r)) x, skInc_mem_puncturedNbhd X r x⟩)
    (fun p => ⟨(topCellMap X r)
        ((cellι X r p.1) (p.2 : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))),
      topCellMap_mem_puncturedNbhd X r p.1 p.2⟩)

@[simp] theorem coe_totMap_inl (x : ↥(SSet.toTop.{u}.obj (Sk X r))) :
    ((totMap X r (Sum.inl x) : ↥(puncturedNbhd X r)) :
      ↥(SSet.toTop.{u}.obj (Sk X (r + 1)))) = (SSet.toTop.map (skInc X r)) x := rfl

@[simp] theorem coe_totMap_inr (s : X.nonDegenerate r) (c : ↥(puncturedCell.{u} r)) :
    ((totMap X r (Sum.inr ⟨s, c⟩) : ↥(puncturedNbhd X r)) :
        ↥(SSet.toTop.{u}.obj (Sk X (r + 1))))
      = (topCellMap X r) ((cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) := rfl

theorem continuous_totMap : Continuous (totMap X r) := by
  refine Continuous.sumElim (((SSet.toTop.map (skInc X r)).hom.continuous).subtype_mk _) ?_
  refine continuous_sigma fun s => ?_
  exact (((topCellMap X r).hom.continuous.comp
    (cellι X r s).hom.continuous).comp continuous_subtype_val).subtype_mk _

theorem surjective_totMap : Function.Surjective (totMap X r) := by
  rintro ⟨z, hz⟩
  rcases jointly_surjective_of_isPushout ((topIsPushout X r).map (forget TopCat.{u})) z with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨Sum.inl a, Subtype.ext ha⟩
  · obtain ⟨s, c, rfl⟩ := exists_ι _ b
    have hc : c ∈ puncturedCell.{u} r := by
      intro hbary
      have hbary' : c = cellBary.{u} r := hbary
      refine hz ⟨s, ?_⟩
      show (topCellMap X r) (cellBaryPt X r s) = z
      rw [cellBaryPt_eq, ← hb, hbary']
      rfl
    exact ⟨Sum.inr ⟨s, ⟨c, hc⟩⟩, Subtype.ext hb⟩

/-- The punctured cell is open in the realized cell. -/
theorem isOpen_puncturedCell : IsOpen (puncturedCell.{u} r) :=
  isOpen_compl_singleton

theorem isOpen_coprod_iff {J : Type u} (A : J → TopCat.{u}) (S : Set ↥(∐ A)) :
    IsOpen S ↔ ∀ j, IsOpen (Limits.Sigma.ι A j ⁻¹' S) := by
  simp only [← isClosed_compl_iff, ← Set.preimage_compl]
  exact isClosed_coprod_iff A Sᶜ

/-- **The quotient presentation.**  `totMap` is a quotient map onto `V`. -/
theorem isQuotientMap_totMap : Topology.IsQuotientMap (totMap X r) := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨surjective_totMap X r, fun W => ⟨fun hW => hW.preimage (continuous_totMap X r), ?_⟩⟩
  intro hW
  set W' : Set ↥(SSet.toTop.obj (Sk X (r + 1))) := Subtype.val '' W with hW'def
  have hpre : W = Subtype.val ⁻¹' W' := by
    ext v
    constructor
    · intro hv; exact ⟨v, hv, rfl⟩
    · rintro ⟨v', hv', hvv⟩
      exact (Subtype.ext hvv : v' = v) ▸ hv'
  have hopen : IsOpen W' := by
    rw [isOpen_iff_of_isPushout (topIsPushout X r)]
    constructor
    · have hEq : (SSet.toTop.map (skInc X r)) ⁻¹' W' = Sum.inl ⁻¹' ((totMap X r) ⁻¹' W) := by
        ext x
        constructor
        · rintro ⟨v, hv, hvx⟩
          have hveq : totMap X r (Sum.inl x) = v := Subtype.ext hvx.symm
          show totMap X r (Sum.inl x) ∈ W
          rw [hveq]; exact hv
        · intro hx
          exact ⟨totMap X r (Sum.inl x), hx, rfl⟩
      rw [hEq]
      exact hW.preimage continuous_inl
    · rw [isOpen_coprod_iff]
      intro s
      have hset : (cellι X r s) ⁻¹' ((topCellMap X r) ⁻¹' W')
          = Subtype.val '' ((fun c : ↥(puncturedCell.{u} r) => (⟨s, c⟩ :
              Σ _ : X.nonDegenerate r, ↥(puncturedCell.{u} r))) ⁻¹'
                (Sum.inr ⁻¹' ((totMap X r) ⁻¹' W))) := by
        ext c
        constructor
        · rintro ⟨v, hv, hvc⟩
          have hcmem : c ∈ puncturedCell.{u} r := by
            intro hbary
            have hbary' : c = cellBary.{u} r := hbary
            refine v.2 ⟨s, ?_⟩
            show (topCellMap X r) (cellBaryPt X r s) = (v : ↥(SSet.toTop.obj (Sk X (r + 1))))
            rw [cellBaryPt_eq, ← hbary', hvc]
          refine ⟨⟨c, hcmem⟩, ?_, rfl⟩
          have hveq : totMap X r (Sum.inr ⟨s, ⟨c, hcmem⟩⟩) = v := Subtype.ext hvc.symm
          show totMap X r (Sum.inr ⟨s, ⟨c, hcmem⟩⟩) ∈ W
          rw [hveq]; exact hv
        · rintro ⟨c', hc', rfl⟩
          exact ⟨totMap X r (Sum.inr ⟨s, c'⟩), hc', rfl⟩
      rw [hset]
      exact (isOpen_puncturedCell r).isOpenMap_subtype_val _
        (hW.preimage (continuous_inr.comp continuous_sigmaMk))
  rw [hpre]
  exact hopen.preimage continuous_subtype_val

/-! ## Descent of maps and homotopies through the quotient presentation -/

variable {X r}

/-- **Descent of a map.**  A continuous map on the total space that respects the identifications
of the pushout descends to a continuous map on `V`. -/
theorem descend {Z : Type u} [TopologicalSpace Z] (g : Tot X r → Z) (hg : Continuous g)
    (hwd : ∀ w w', totMap X r w = totMap X r w' → g w = g w') :
    ∃ f : C(↥(puncturedNbhd X r), Z), ∀ w, f (totMap X r w) = g w := by
  classical
  refine ⟨⟨fun v => g (Function.surjInv (surjective_totMap X r) v), ?_⟩, fun w => ?_⟩
  · rw [(isQuotientMap_totMap X r).continuous_iff]
    have hcomp : (fun w => g (Function.surjInv (surjective_totMap X r) (totMap X r w))) = g := by
      funext w
      exact hwd _ _ (Function.surjInv_eq (surjective_totMap X r) (totMap X r w))
    rw [Function.comp_def, hcomp]
    exact hg
  · exact hwd _ _ (Function.surjInv_eq (surjective_totMap X r) (totMap X r w))

/-- **Descent of a homotopy.**  Joint continuity is obtained from the pinned lifting theorem for
quotient maps against a locally compact factor. -/
theorem descendHomotopy {Z : Type u} [TopologicalSpace Z] (G : unitInterval × Tot X r → Z)
    (hG : Continuous G)
    (hwd : ∀ (t : unitInterval) (w w' : Tot X r),
      totMap X r w = totMap X r w' → G (t, w) = G (t, w')) :
    ∃ F : C(unitInterval × ↥(puncturedNbhd X r), Z),
      ∀ (t : unitInterval) (w : Tot X r), F (t, totMap X r w) = G (t, w) := by
  classical
  refine ⟨⟨fun p => G (p.1, Function.surjInv (surjective_totMap X r) p.2), ?_⟩, fun t w => ?_⟩
  · refine (isQuotientMap_totMap X r).continuous_lift_prod_right ?_
    have hcomp : (fun p : unitInterval × Tot X r =>
        G (p.1, Function.surjInv (surjective_totMap X r) (totMap X r p.2))) = G := by
      funext p
      exact hwd p.1 _ _ (Function.surjInv_eq (surjective_totMap X r) (totMap X r p.2))
    rw [hcomp]
    exact hG
  · exact hwd t _ _ (Function.surjInv_eq (surjective_totMap X r) (totMap X r w))

/-! ## Continuity criteria for maps out of a product with a sum or a sigma -/

theorem continuous_prod_sum {W A B Z : Type*} [TopologicalSpace W] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace Z] {G : W × (A ⊕ B) → Z}
    (h1 : Continuous fun p : W × A => G (p.1, Sum.inl p.2))
    (h2 : Continuous fun p : W × B => G (p.1, Sum.inr p.2)) : Continuous G := by
  have hG : G = (Sum.elim (fun p : W × A => G (p.1, Sum.inl p.2))
      (fun p : W × B => G (p.1, Sum.inr p.2))) ∘ (Homeomorph.prodSumDistrib (X := W) (Y := A)
        (Z := B)) := by
    funext p
    obtain ⟨w, a | b⟩ := p <;> rfl
  rw [hG]
  exact (h1.sumElim h2).comp (Homeomorph.prodSumDistrib (X := W) (Y := A) (Z := B)).continuous

theorem continuous_prod_sigma {W Z : Type*} {J : Type*} {C : J → Type*} [TopologicalSpace W]
    [TopologicalSpace Z] [∀ j, TopologicalSpace (C j)] {G : W × (Σ j, C j) → Z}
    (h : ∀ j, Continuous fun p : W × C j => G (p.1, ⟨j, p.2⟩)) : Continuous G := by
  have hG : G = ((fun q : Σ j, C j × W => G (q.2.2, ⟨q.1, q.2.1⟩)) ∘
      (Homeomorph.sigmaProdDistrib (X := C) (Y := W))) ∘ (Homeomorph.prodComm W (Σ j, C j)) := by
    funext p
    obtain ⟨w, ⟨j, c⟩⟩ := p
    rfl
  rw [hG]
  refine Continuous.comp (Continuous.comp ?_ (Homeomorph.sigmaProdDistrib).continuous)
    (Homeomorph.prodComm W (Σ j, C j)).continuous
  exact continuous_sigma fun j => (h j).comp (continuous_snd.prodMk continuous_fst)

/-! ## The retraction of `V` onto the old skeleton -/

variable (X r)

/-- The retraction data on the total space: the identity on the old skeleton, and the radial
retraction followed by the attaching map on each punctured cell. -/
def retrTot : Tot X r → ↥(SSet.toTop.{u}.obj (Sk X r)) :=
  Sum.elim id (fun p => (SSet.toTop.map (cellAttach X r p.1)) (cellRetract.{u} r p.2))

theorem continuous_retrTot : Continuous (retrTot X r) := by
  refine Continuous.sumElim continuous_id (continuous_sigma fun s => ?_)
  exact (SSet.toTop.map (cellAttach X r s)).hom.continuous.comp (cellRetract.{u} r).continuous

/-- The realized skeletal inclusion is injective (Task 15/16). -/
theorem skInc_injective : Function.Injective (SSet.toTop.map (skInc X r)) :=
  SpineTask15.realization_skInc_injective X r (SpineTask16.standardCellMono.{u} r)

/-- If a point of a cell is identified with a point of the old skeleton, it is a boundary
point, and the identification is through the attaching map. -/
theorem exists_bdry_of_totMap_inl_inr {x : ↥(SSet.toTop.{u}.obj (Sk X r))}
    {s : X.nonDegenerate r} {c : ↥(puncturedCell.{u} r)}
    (h : totMap X r (Sum.inl x) = totMap X r (Sum.inr ⟨s, c⟩)) :
    ∃ b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})),
      cellBdryIncl.{u} r b = (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) ∧
        (SSet.toTop.map (cellAttach X r s)) b = x := by
  have h' : (topCellMap X r) ((cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))))
      = (SSet.toTop.map (skInc X r)) x := (congrArg Subtype.val h).symm
  obtain ⟨w, hw1, hw2⟩ := (topCellMap_eq_skInc_iff X r _ _).1 h'
  obtain ⟨t, b, rfl⟩ := exists_ι _ w
  have hwb : (cellι X r t) ((SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) b)
      = (cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :=
    (topBdryMap_bdryι X r t b).symm.trans hw1
  have hts : t = s := ι_eq_component _ hwb
  subst hts
  refine ⟨b, ι_injective _ _ hwb, ?_⟩
  exact (topAttachMap_bdryι X r t b).symm.trans hw2

/-- A punctured point which lies on the boundary is the image of that boundary point. -/
theorem eq_bdryToPunctured {c : ↥(puncturedCell.{u} r)}
    {b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))}
    (hb : cellBdryIncl.{u} r b = (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) :
    c = bdryToPunctured.{u} r b :=
  Subtype.ext hb.symm

theorem cellRetract_of_bdry {c : ↥(puncturedCell.{u} r)}
    {b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))}
    (hb : cellBdryIncl.{u} r b = (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) :
    cellRetract.{u} r c = b := by
  rw [eq_bdryToPunctured r hb, cellRetract_bdryToPunctured]

/-- **Well-definedness of the retraction.** -/
theorem retrTot_wd (w w' : Tot X r) (h : totMap X r w = totMap X r w') :
    retrTot X r w = retrTot X r w' := by
  match w, w' with
  | Sum.inl x, Sum.inl x' =>
      exact skInc_injective X r (congrArg Subtype.val h)
  | Sum.inl x, Sum.inr ⟨s, c⟩ =>
      obtain ⟨b, hb, hbx⟩ := exists_bdry_of_totMap_inl_inr X r h
      show x = (SSet.toTop.map (cellAttach X r s)) (cellRetract.{u} r c)
      rw [cellRetract_of_bdry r hb, hbx]
  | Sum.inr ⟨s, c⟩, Sum.inl x =>
      obtain ⟨b, hb, hbx⟩ := exists_bdry_of_totMap_inl_inr X r h.symm
      show (SSet.toTop.map (cellAttach X r s)) (cellRetract.{u} r c) = x
      rw [cellRetract_of_bdry r hb, hbx]
  | Sum.inr ⟨s, c⟩, Sum.inr ⟨s', c'⟩ =>
      have h' : (topCellMap X r) ((cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))))
          = (topCellMap X r) ((cellι X r s')
            (c' : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) := congrArg Subtype.val h
      rcases (inl_eq_inl_iff_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r)
        _ _).1 h' with heq | ⟨w, w', hww', hw, hw'⟩
      · obtain rfl : s = s' := ι_eq_component _ heq
        obtain rfl : c = c' := Subtype.ext (ι_injective _ _ heq)
        rfl
      · obtain ⟨t, b, rfl⟩ := exists_ι _ w
        obtain ⟨t', b', rfl⟩ := exists_ι _ w'
        have hwb := hw.trans (topBdryMap_bdryι X r t b)
        have hwb' := hw'.trans (topBdryMap_bdryι X r t' b')
        have hts : s = t := ι_eq_component _ hwb
        have hts' : s' = t' := ι_eq_component _ hwb'
        subst hts
        subst hts'
        have hb : cellBdryIncl.{u} r b = (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :=
          (ι_injective _ _ hwb).symm
        have hb' : cellBdryIncl.{u} r b' = (c' : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :=
          (ι_injective _ _ hwb').symm
        show (SSet.toTop.map (cellAttach X r s)) (cellRetract.{u} r c)
          = (SSet.toTop.map (cellAttach X r s')) (cellRetract.{u} r c')
        rw [cellRetract_of_bdry r hb, cellRetract_of_bdry r hb', ← topAttachMap_bdryι,
          ← topAttachMap_bdryι]
        exact hww'

/-- **WP3, the retraction.**  `V ⟶ A`. -/
def vRetract : C(↥(puncturedNbhd X r), ↥(SSet.toTop.{u}.obj (Sk X r))) :=
  (descend (retrTot X r) (continuous_retrTot X r) (retrTot_wd X r)).choose

theorem vRetract_totMap (w : Tot X r) : vRetract X r (totMap X r w) = retrTot X r w :=
  (descend (retrTot X r) (continuous_retrTot X r) (retrTot_wd X r)).choose_spec w

/-- **WP3, the inclusion.**  `A ⟶ V`. -/
def skToV : C(↥(SSet.toTop.{u}.obj (Sk X r)), ↥(puncturedNbhd X r)) where
  toFun x := totMap X r (Sum.inl x)
  continuous_toFun := (continuous_totMap X r).comp continuous_inl

/-- **The retraction is a retraction.** -/
theorem vRetract_skToV (x : ↥(SSet.toTop.{u}.obj (Sk X r))) :
    vRetract X r (skToV X r x) = x :=
  vRetract_totMap X r (Sum.inl x)

/-! ## The descended homotopy -/

/-- The homotopy data on the total space. -/
def homTot : unitInterval × Tot X r → ↥(puncturedNbhd X r) := fun p =>
  Sum.elim (fun x => totMap X r (Sum.inl x))
    (fun q : Σ _ : X.nonDegenerate r, ↥(puncturedCell.{u} r) =>
      totMap X r (Sum.inr ⟨q.1, cellHomotopy.{u} r (p.1, q.2)⟩)) p.2

theorem continuous_homTot : Continuous (homTot X r) := by
  refine continuous_prod_sum ?_ ?_
  · exact ((continuous_totMap X r).comp continuous_inl).comp continuous_snd
  · refine continuous_prod_sigma (C := fun _ : X.nonDegenerate r => ↥(puncturedCell.{u} r))
      fun s => ?_
    refine ((continuous_totMap X r).comp continuous_inr).comp ?_
    refine continuous_sigmaMk.comp ?_
    exact (cellHomotopy.{u} r).continuous.comp (continuous_fst.prodMk continuous_snd)

/-- On a boundary point the descended homotopy is constant. -/
theorem homTot_of_bdry (t : unitInterval) (s : X.nonDegenerate r) (c : ↥(puncturedCell.{u} r))
    (hc : ∃ b, cellBdryIncl.{u} r b = (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) :
    homTot X r (t, Sum.inr ⟨s, c⟩) = totMap X r (Sum.inr ⟨s, c⟩) := by
  obtain ⟨b, hb⟩ := hc
  show totMap X r (Sum.inr ⟨s, cellHomotopy.{u} r (t, c)⟩) = totMap X r (Sum.inr ⟨s, c⟩)
  rw [eq_bdryToPunctured r hb, cellHomotopy_bdry]

/-- **Well-definedness of the homotopy.** -/
theorem homTot_wd (t : unitInterval) (w w' : Tot X r) (h : totMap X r w = totMap X r w') :
    homTot X r (t, w) = homTot X r (t, w') := by
  match w, w' with
  | Sum.inl x, Sum.inl x' =>
      obtain rfl : x = x' := skInc_injective X r (congrArg Subtype.val h)
      rfl
  | Sum.inl x, Sum.inr ⟨s, c⟩ =>
      obtain ⟨b, hb, -⟩ := exists_bdry_of_totMap_inl_inr X r h
      rw [homTot_of_bdry X r t s c ⟨b, hb⟩]
      exact h
  | Sum.inr ⟨s, c⟩, Sum.inl x =>
      obtain ⟨b, hb, -⟩ := exists_bdry_of_totMap_inl_inr X r h.symm
      rw [homTot_of_bdry X r t s c ⟨b, hb⟩]
      exact h
  | Sum.inr ⟨s, c⟩, Sum.inr ⟨s', c'⟩ =>
      have h' : (topCellMap X r) ((cellι X r s) (c : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))))
          = (topCellMap X r) ((cellι X r s')
            (c' : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))) := congrArg Subtype.val h
      rcases (inl_eq_inl_iff_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r)
        _ _).1 h' with heq | ⟨w0, w0', -, hw0, hw0'⟩
      · obtain rfl : s = s' := ι_eq_component _ heq
        obtain rfl : c = c' := Subtype.ext (ι_injective _ _ heq)
        rfl
      · obtain ⟨t0, b0, rfl⟩ := exists_ι _ w0
        obtain ⟨t0', b0', rfl⟩ := exists_ι _ w0'
        have hwb0 := hw0.trans (topBdryMap_bdryι X r t0 b0)
        have hwb0' := hw0'.trans (topBdryMap_bdryι X r t0' b0')
        have hts : s = t0 := ι_eq_component _ hwb0
        have hts' : s' = t0' := ι_eq_component _ hwb0'
        subst hts
        subst hts'
        rw [homTot_of_bdry X r t s c ⟨b0, (ι_injective _ _ hwb0).symm⟩,
          homTot_of_bdry X r t s' c' ⟨b0', (ι_injective _ _ hwb0').symm⟩]
        exact h

/-- **WP3, the homotopy.**  `[0,1] × V ⟶ V`. -/
def vHomotopy : C(unitInterval × ↥(puncturedNbhd X r), ↥(puncturedNbhd X r)) :=
  (descendHomotopy (homTot X r) (continuous_homTot X r) (homTot_wd X r)).choose

theorem vHomotopy_totMap (t : unitInterval) (w : Tot X r) :
    vHomotopy X r (t, totMap X r w) = homTot X r (t, w) :=
  (descendHomotopy (homTot X r) (continuous_homTot X r) (homTot_wd X r)).choose_spec t w

/-- **The homotopy starts at the identity of `V`.** -/
theorem vHomotopy_zero (v : ↥(puncturedNbhd X r)) : vHomotopy X r (0, v) = v := by
  obtain ⟨w, rfl⟩ := surjective_totMap X r v
  rw [vHomotopy_totMap]
  match w with
  | Sum.inl x => rfl
  | Sum.inr ⟨s, c⟩ =>
      show totMap X r (Sum.inr ⟨s, cellHomotopy.{u} r (0, c)⟩) = totMap X r (Sum.inr ⟨s, c⟩)
      rw [cellHomotopy_zero]

/-- **The homotopy fixes the old skeleton pointwise.** -/
theorem vHomotopy_fix (t : unitInterval) (x : ↥(SSet.toTop.{u}.obj (Sk X r))) :
    vHomotopy X r (t, skToV X r x) = skToV X r x :=
  vHomotopy_totMap X r t (Sum.inl x)

/-- **The homotopy ends at the retraction.** -/
theorem vHomotopy_one (v : ↥(puncturedNbhd X r)) :
    vHomotopy X r (1, v) = skToV X r (vRetract X r v) := by
  obtain ⟨w, rfl⟩ := surjective_totMap X r v
  rw [vHomotopy_totMap, vRetract_totMap]
  match w with
  | Sum.inl x => rfl
  | Sum.inr ⟨s, c⟩ =>
      refine Subtype.ext ?_
      show (topCellMap X r) ((cellι X r s)
          ((cellHomotopy.{u} r (1, c) : ↥(puncturedCell.{u} r)) :
            ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))))
        = (SSet.toTop.map (skInc X r))
          ((SSet.toTop.map (cellAttach X r s)) (cellRetract.{u} r c))
      rw [cellHomotopy_one, topCellMap_cellι]
      exact cellChar_bdry X r s (cellRetract.{u} r c)

end Descent

end SpineTask23
