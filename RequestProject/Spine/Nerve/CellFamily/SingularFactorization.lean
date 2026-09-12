import RequestProject.Spine.AlgebraicTopology.Excision
import RequestProject.Spine.Nerve.Geometry.CellNeighborhood
import RequestProject.Spine.Nerve.Geometry.OpenStandardCell

/-!
# Task 23, WP6 (geometric half) — the union of the open cells is the disjoint union of the cells

With `Y = |Sk X (r+1)|`, `A = |Sk X r|` and `U = Y \ A` (the union of the newly attached open
cells), this module proves that `U` is, as a topological space, the disjoint union of the
finitely many open standard cells `Δ° = |Δ[r]| \ |∂Δ[r]|`, one for each nondegenerate
`r`-simplex.  Precisely, it produces the family of maps

`cellIncl X r σ : Δ° → U`

induced by the realized characteristic maps, and proves that they are continuous, injective,
have pairwise disjoint open images covering `U`; consequently every singular simplex of `U`
factors, uniquely, through exactly one of them (`exists_cellIncl_lift`), the geometric simplex
`Δs q` being connected.

The two statements exported for the chain-level argument are

* `bijective_cellSingMap` — `X.nonDegenerate r × Sing Δ° q ≃ Sing U q`;
* `cellSingMap_mem_range_incInterU_iff` — a singular simplex of `U` lands in `V = Y \ B` exactly
  when its lift lands in the punctured cell `|Δ[r]| \ {b_r}`.

No finiteness of the cell family is used here; the openness of the images comes from the
Task-15 realized pushout via `TopCat.isOpen_iff_of_isColimit` (see `Task23SkeletonTopology`).
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask15 SpineTask17
  SpineTask18

universe u

namespace SpineTask23

/-! ## Joint surjectivity of the two legs of a pushout of types -/

theorem range_union_range_of_isPushout {W A B Y : Type u} {f : W ⟶ A} {g : W ⟶ B} {i : A ⟶ Y}
    {j : B ⟶ Y} (h : IsPushout f g i j) : Set.range i ∪ Set.range j = Set.univ := by
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
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨w, hw⟩ : ∃ w, e.inv w = z := ⟨e.hom z, congrFun e.hom_inv_id z⟩
  obtain ⟨a | b⟩ := w
  · refine Or.inl ⟨a, hinj ?_⟩
    rw [hi, ← hw]
    exact (congrFun e.inv_hom_id _).symm
  · refine Or.inr ⟨b, hinj ?_⟩
    rw [hj, ← hw]
    exact (congrFun e.inv_hom_id _).symm

/-! ## Singular simplices and induced maps -/

theorem sMap_toSSet_map_apply {Z W : TopCat.{u}} (g : Z ⟶ W) {q : ℕ} (s : Sing Z q) (x : Δs q) :
    sMap ((TopCat.toSSet.map g).app (op (SimplexCategory.mk q)) s) x = g (sMap s x) := rfl

theorem sing_ext {Z : TopCat.{u}} {q : ℕ} {s t : Sing Z q} (h : ∀ x, sMap s x = sMap t x) :
    s = t := by
  have : sMap s = sMap t := ContinuousMap.ext h
  rw [← sOf_sMap s, ← sOf_sMap t, this]

/-- A singular simplex of `subTop (U ∩ V)`-fame: membership in the range of the inclusion
`U ∩ V ↪ U` is exactly the condition that all values lie in `V`. -/
theorem mem_range_incInterU_iff {Z : TopCat.{u}} (U V : Set Z) {q : ℕ}
    (s : Sing (subTop U) q) :
    s ∈ Set.range ((TopCat.toSSet.map (incInterU U V)).app (op (SimplexCategory.mk q)))
      ↔ ∀ x, ((sMap s x : U) : Z) ∈ V := by
  constructor
  · rintro ⟨t, rfl⟩ x
    have h : sMap ((TopCat.toSSet.map (incInterU U V)).app (op (SimplexCategory.mk q)) t) x
        = ⟨((sMap t x : ↥(U ∩ V)) : Z), (sMap t x).2.1⟩ := rfl
    rw [h]
    exact (sMap t x).2.2
  · intro h
    refine mem_range_incInterU U V s ?_
    rintro _ ⟨x, rfl⟩
    have hx : sMap ((TopCat.toSSet.map (subInc U)).app (op (SimplexCategory.mk q)) s) x
        = ((sMap s x : U) : Z) := rfl
    rw [hx]
    exact h x

/-! ## The open cells -/

section Cells

variable (X : SSet.{u}) (r : ℕ)

/-- The point of `Y = |Sk X (r+1)|` determined by a point of the `σ`-cell. -/
def cellPt (σ : X.nonDegenerate r) (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    ↥(SSet.toTop.{u}.obj (Sk X (r + 1))) :=
  topCellMap X r
    ((Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x)

theorem cellPt_eq (σ : X.nonDegenerate r) (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    cellPt X r σ x = SSet.toTop.map (cellChar X r σ) x :=
  ConcreteCategory.congr_hom
    (Limits.Sigma.ι_desc (fun σ : X.nonDegenerate r => SSet.toTop.map (cellChar X r σ)) σ) x

theorem continuous_cellPt (σ : X.nonDegenerate r) : Continuous (cellPt X r σ) := by
  have h : cellPt X r σ = fun x => SSet.toTop.map (cellChar X r σ) x :=
    funext fun x => cellPt_eq X r σ x
  rw [h]
  exact (SSet.toTop.map (cellChar X r σ)).hom.continuous

theorem mem_range_topBdryMap_iff (σ : X.nonDegenerate r)
    (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    (Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x
        ∈ Set.range (topBdryMap X r)
      ↔ x ∈ Set.range (SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) := by
  constructor
  · intro hx
    have h : x ∈ (Limits.Sigma.ι
        (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) ⁻¹'
          (Set.range (topBdryMap X r)) := hx
    rw [topBdryMap, preimage_ι_range_sigmaMap] at h
    exact h
  · intro hx
    have h : x ∈ Set.range ((fun _ : X.nonDegenerate r =>
        SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) σ) := hx
    rw [← preimage_ι_range_sigmaMap
      (fun _ : X.nonDegenerate r => SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) σ]
      at h
    exact h

theorem cellPt_mem_openCells {σ : X.nonDegenerate r} {x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))}
    (hx : x ∈ openStdCell.{u} r) : cellPt X r σ x ∈ openCells X r := by
  intro hmem
  have h : (Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x
      ∈ (topCellMap X r) ⁻¹' (Set.range (SSet.toTop.map (skInc X r))) := hmem
  rw [preimage_topCellMap_range_skInc, mem_range_topBdryMap_iff] at h
  exact hx h

theorem mem_openStdCell_of_cellPt {σ : X.nonDegenerate r}
    {x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))} (hx : cellPt X r σ x ∈ openCells X r) :
    x ∈ openStdCell.{u} r := by
  intro hmem
  refine hx ?_
  have h : (Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x
      ∈ Set.range (topBdryMap X r) := (mem_range_topBdryMap_iff X r σ x).2 hmem
  obtain ⟨w, hw⟩ := h
  refine ⟨topAttachMap X r w, ?_⟩
  have := (topCellMap_eq_skInc_iff X r _ (topAttachMap X r w)).2 ⟨w, hw, rfl⟩
  exact this.symm

/-- **The `σ`-th open cell inclusion** `Δ° → U`. -/
def cellIncl (σ : X.nonDegenerate r) : C(↥(openStdCell.{u} r), ↥(openCells X r)) where
  toFun x := ⟨cellPt X r σ x.1, cellPt_mem_openCells X r x.2⟩
  continuous_toFun :=
    ((continuous_cellPt X r σ).comp continuous_subtype_val).subtype_mk _

@[simp] theorem cellIncl_coe (σ : X.nonDegenerate r) (x : ↥(openStdCell.{u} r)) :
    ((cellIncl X r σ x : ↥(openCells X r)) : ↥(SSet.toTop.{u}.obj (Sk X (r + 1))))
      = cellPt X r σ x.1 := rfl

/-- Points of the open cells are separated: the `σ` and the point are both determined. -/
theorem cellPt_inj {σ τ : X.nonDegenerate r} {x y : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))}
    (hx : x ∈ openStdCell.{u} r) (h : cellPt X r σ x = cellPt X r τ y) :
    σ = τ ∧ x = y := by
  have hnb : (Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x
      ∉ Set.range (topBdryMap X r) := fun hmem =>
    hx ((mem_range_topBdryMap_iff X r σ x).1 hmem)
  have heq := inl_injOn_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r) hnb h
  have hσ : σ = τ := ι_eq_component _ heq
  subst hσ
  exact ⟨rfl, ι_injective _ _ heq⟩

theorem cellIncl_injective (σ : X.nonDegenerate r) : Function.Injective (cellIncl X r σ) := by
  intro x y h
  have h' : cellPt X r σ x.1 = cellPt X r σ y.1 := congrArg Subtype.val h
  exact Subtype.ext (cellPt_inj X r x.2 h').2

theorem cellIncl_component {σ τ : X.nonDegenerate r} {x y : ↥(openStdCell.{u} r)}
    (h : cellIncl X r σ x = cellIncl X r τ y) : σ = τ :=
  (cellPt_inj X r x.2 (congrArg Subtype.val h)).1

/-! ### Openness -/

theorem isOpen_image_topCellMap (W : Set ↥(topAttachTgt X r)) (hW : IsOpen W)
    (hWb : ∀ w ∈ W, w ∉ Set.range (topBdryMap X r)) :
    IsOpen (topCellMap X r '' W) := by
  rw [isOpen_iff_of_isPushout (topIsPushout X r)]
  constructor
  · have hempty : (SSet.toTop.map (skInc X r)) ⁻¹' (topCellMap X r '' W) = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨w, hw, hwz⟩
      obtain ⟨v, hv, -⟩ := (topCellMap_eq_skInc_iff X r w z).1 hwz
      exact hWb w hw ⟨v, hv⟩
    rw [hempty]
    exact isOpen_empty
  · have hpre : (topCellMap X r) ⁻¹' (topCellMap X r '' W) = W := by
      ext y
      constructor
      · rintro ⟨w, hw, hwy⟩
        have : w = y := inl_injOn_of_isPushout (typeIsPushout X r) (topBdryMap_injective X r)
          (hWb w hw) hwy
        rwa [← this]
      · exact fun hy => ⟨y, hy, rfl⟩
    rw [hpre]
    exact hW

theorem isOpenMap_sigmaι (σ : X.nonDegenerate r) :
    IsOpenMap (Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) := by
  set e := TopCat.sigmaIsoSigma
    (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) with he
  have hcomp : (Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ)
      = (TopCat.homeoOfIso e.symm) ∘ (Sigma.mk σ) := by
    funext x
    show (Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x
        = (ConcreteCategory.hom e.inv) ⟨σ, x⟩
    exact (TopCat.sigmaIsoSigma_inv_apply
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ x).symm
  rw [hcomp]
  exact IsOpenMap.comp (TopCat.homeoOfIso e.symm).isOpenMap isOpenMap_sigmaMk

theorem isOpenMap_cellIncl (σ : X.nonDegenerate r) : IsOpenMap (cellIncl X r σ) := by
  intro W hW
  rw [isOpen_induced_iff] at hW
  obtain ⟨W', hW', hWW'⟩ := hW
  set S : Set ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})) := W' ∩ openStdCell.{u} r with hS
  have hSopen : IsOpen S := hW'.inter (isOpen_openStdCell.{u} r)
  have hmemS : ∀ x : ↥(openStdCell.{u} r), x.1 ∈ S ↔ x ∈ W := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ Subtype.val ⁻¹' W' := hx.1
      rw [hWW'] at hx'
      exact hx'
    · intro hx
      refine ⟨?_, x.2⟩
      rw [← hWW'] at hx
      exact hx
  set T : Set ↥(topAttachTgt X r) :=
    (Limits.Sigma.ι (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) '' S
    with hT
  have hTopen : IsOpen T := isOpenMap_sigmaι X r σ S hSopen
  have hTb : ∀ w ∈ T, w ∉ Set.range (topBdryMap X r) := by
    rintro _ ⟨x, hx, rfl⟩ hmem
    exact hx.2 ((mem_range_topBdryMap_iff X r σ x).1 hmem)
  have himg : IsOpen (topCellMap X r '' T) := isOpen_image_topCellMap X r T hTopen hTb
  rw [isOpen_induced_iff]
  refine ⟨topCellMap X r '' T, himg, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨x, hxS, rfl⟩ := hw
    refine ⟨⟨x, hxS.2⟩, (hmemS ⟨x, hxS.2⟩).1 hxS, ?_⟩
    exact Subtype.ext hwz
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Limits.Sigma.ι
      (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x.1,
      ⟨x.1, (hmemS x).2 hx, rfl⟩, rfl⟩

/-! ### The cells cover `U` -/

theorem exists_cellIncl (z : ↥(openCells X r)) :
    ∃ (σ : X.nonDegenerate r) (x : ↥(openStdCell.{u} r)), cellIncl X r σ x = z := by
  have hcover := range_union_range_of_isPushout (typeIsPushout X r)
  have hz : z.1 ∈ Set.range ((forget TopCat).map (topCellMap X r))
      ∪ Set.range ((forget TopCat).map (SSet.toTop.map (skInc X r))) := by
    rw [hcover]; trivial
  rcases hz with ⟨y, hy⟩ | ⟨w, hw⟩
  · obtain ⟨σ, x, rfl⟩ := exists_ι _ y
    have hy' : cellPt X r σ x = z.1 := hy
    have hx : x ∈ openStdCell.{u} r := by
      refine mem_openStdCell_of_cellPt (σ := σ) X r ?_
      rw [hy']
      exact z.2
    exact ⟨σ, ⟨x, hx⟩, Subtype.ext hy'⟩
  · exact absurd ⟨w, hw⟩ z.2

/-! ### The barycentres -/

theorem cellPt_bary (σ : X.nonDegenerate r) :
    cellPt X r σ (cellBary.{u} r) = baryPoint X r σ := rfl

theorem cellPt_mem_barySet_iff (σ : X.nonDegenerate r)
    (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    cellPt X r σ x ∈ barySet X r ↔ x = cellBary.{u} r := by
  constructor
  · intro hmem
    have h : (Limits.Sigma.ι
        (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) x
        ∈ (topCellMap X r) ⁻¹' (barySet X r) := hmem
    rw [preimage_topCellMap_barySet] at h
    have h' : x ∈ (Limits.Sigma.ι
        (fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})) σ) ⁻¹'
          (Set.range (cellBaryPt X r)) := h
    rw [preimage_ι_range_cellBaryPt] at h'
    exact h'
  · rintro rfl
    exact ⟨σ, rfl⟩

theorem cellIncl_mem_puncturedNbhd_iff (σ : X.nonDegenerate r) (x : ↥(openStdCell.{u} r)) :
    ((cellIncl X r σ x : ↥(openCells X r)) : ↥(SSet.toTop.{u}.obj (Sk X (r + 1))))
        ∈ puncturedNbhd X r
      ↔ (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) ∈ puncturedCell.{u} r := by
  show cellPt X r σ x.1 ∉ barySet X r ↔ ¬ (x.1 = cellBary.{u} r)
  rw [cellPt_mem_barySet_iff]

/-! ### Factorisation of a singular simplex of `U` through a single cell -/

instance preconnectedSpace_Δs (q : ℕ) : PreconnectedSpace (Δs q) :=
  Subtype.preconnectedSpace ((convex_stdSimplex ℝ (Fin (q + 1))).isPreconnected)

theorem exists_cellIncl_lift {q : ℕ} (τ : C(Δs q, ↥(openCells X r))) :
    ∃ (σ : X.nonDegenerate r) (g : C(Δs q, ↥(openStdCell.{u} r))),
      (cellIncl X r σ).comp g = τ := by
  classical
  set x₀ : Δs q := stdSimplex.vertex 0 with hx₀
  obtain ⟨σ, x₁, hx₁⟩ := exists_cellIncl X r (τ x₀)
  haveI : Nonempty ↥(openStdCell.{u} r) := ⟨x₁⟩
  set A : Set (Δs q) := τ ⁻¹' (Set.range (cellIncl X r σ)) with hA
  have hrange : ∀ t : X.nonDegenerate r, IsOpen (Set.range (cellIncl X r t)) := by
    intro t
    rw [← Set.image_univ]
    exact isOpenMap_cellIncl X r t Set.univ isOpen_univ
  have hAopen : IsOpen A := (hrange σ).preimage τ.continuous
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
    obtain ⟨t, xt, hxt⟩ := exists_cellIncl X r (τ y)
    have hts : t ≠ σ := by
      rintro rfl
      exact hy ⟨xt, hxt⟩
    refine ⟨τ ⁻¹' (Set.range (cellIncl X r t)), ?_, (hrange t).preimage τ.continuous,
      ⟨xt, hxt⟩⟩
    rintro z ⟨xz, hxz⟩ ⟨wz, hwz⟩
    exact hts (cellIncl_component X r (hxz.trans hwz.symm))
  have hAne : A.Nonempty := ⟨x₀, x₁, hx₁⟩
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  have hmem : ∀ y : Δs q, ∃ x, cellIncl X r σ x = τ y := by
    intro y
    have : y ∈ A := by rw [hAuniv]; trivial
    exact this
  set g : Δs q → ↥(openStdCell.{u} r) :=
    fun y => Function.invFun (cellIncl X r σ) (τ y) with hg
  have hgeq : ∀ y, cellIncl X r σ (g y) = τ y :=
    fun y => Function.invFun_eq (hmem y)
  have hemb : Topology.IsOpenEmbedding (cellIncl X r σ) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (cellIncl X r σ).continuous (cellIncl_injective X r σ) (isOpenMap_cellIncl X r σ)
  have hgc : Continuous g := by
    refine hemb.isInducing.continuous_iff.2 ?_
    have : (cellIncl X r σ) ∘ g = τ := funext hgeq
    rw [this]
    exact τ.continuous
  exact ⟨σ, ⟨g, hgc⟩, ContinuousMap.ext hgeq⟩

/-! ### The singular simplices of `U` -/

/-- The `σ`-th open cell inclusion, as a morphism of `TopCat`. -/
def cellInclMap (σ : X.nonDegenerate r) :
    subTop (openStdCell.{u} r) ⟶ subTop (openCells X r) :=
  TopCat.ofHom (cellIncl X r σ)

/-- The map `(σ, singular simplex of Δ°) ↦ singular simplex of U`. -/
def cellSingMap (q : ℕ)
    (p : X.nonDegenerate r × Sing (subTop (openStdCell.{u} r)) q) :
    Sing (subTop (openCells X r)) q :=
  (TopCat.toSSet.map (cellInclMap X r p.1)).app (op (SimplexCategory.mk q)) p.2

theorem sMap_cellSingMap (q : ℕ) (σ : X.nonDegenerate r)
    (s : Sing (subTop (openStdCell.{u} r)) q) (x : Δs q) :
    sMap (cellSingMap X r q (σ, s)) x = cellIncl X r σ (sMap s x) := rfl

/-- **WP6, the combinatorial statement.**  Every singular simplex of `U` is the image of a
unique singular simplex of the standard open cell under a unique cell inclusion. -/
theorem bijective_cellSingMap (q : ℕ) : Function.Bijective (cellSingMap X r q) := by
  constructor
  · rintro ⟨σ, s⟩ ⟨τ, t⟩ h
    have hpt : ∀ x : Δs q, cellIncl X r σ (sMap s x) = cellIncl X r τ (sMap t x) := by
      intro x
      rw [← sMap_cellSingMap, ← sMap_cellSingMap, h]
    have hστ : σ = τ := cellIncl_component X r (hpt (stdSimplex.vertex 0))
    subst hστ
    refine Prod.ext rfl ?_
    refine sing_ext fun x => ?_
    exact cellIncl_injective X r σ (hpt x)
  · intro u
    obtain ⟨σ, g, hg⟩ := exists_cellIncl_lift X r (sMap u)
    refine ⟨⟨σ, sOf g⟩, sing_ext fun x => ?_⟩
    rw [sMap_cellSingMap, sMap_sOf]
    exact congrFun (congrArg (fun f : C(Δs q, ↥(openCells X r)) => (f : Δs q → _)) hg) x

/-- **WP6, the relative statement.**  A singular simplex of `U` lands in `V = Y \ B` exactly
when its lift lands in the punctured standard cell. -/
theorem cellSingMap_mem_range_incInterU_iff (q : ℕ) (σ : X.nonDegenerate r)
    (s : Sing (subTop (openStdCell.{u} r)) q) :
    cellSingMap X r q (σ, s) ∈ Set.range ((TopCat.toSSet.map
        (incInterU (openCells X r) (puncturedNbhd X r))).app (op (SimplexCategory.mk q)))
      ↔ s ∈ Set.range ((TopCat.toSSet.map
        (incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).app
          (op (SimplexCategory.mk q))) := by
  rw [mem_range_incInterU_iff, mem_range_incInterU_iff]
  constructor
  · intro h x
    have hx := h x
    rw [sMap_cellSingMap] at hx
    exact (cellIncl_mem_puncturedNbhd_iff X r σ (sMap s x)).1 hx
  · intro h x
    rw [sMap_cellSingMap]
    exact (cellIncl_mem_puncturedNbhd_iff X r σ (sMap s x)).2 (h x)

end Cells

end SpineTask23
