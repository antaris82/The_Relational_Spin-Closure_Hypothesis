import RequestProject.Spine.Nerve.Skeleton.RealizationMono

/-!
# Task 16 — a point model for geometric realization, and the standard-cell monomorphism

This module opens up the *points* of the geometric realization `SSet.toTop` of the pinned
Mathlib (`Mathlib/AlgebraicTopology/SingularSet.lean`), where `SSet.toTop` is defined as the
left Kan extension `stdSimplex.leftKanExtension SimplexCategory.toTop` and is never evaluated.

The strategy is to *not* replace the realization functor by any other model:

* `SpineTask16.exists_representative` (Level A) : every point of `|A|` (as a set, i.e. under
  `SpineTask15.Real = SSet.toTop ⋙ forget TopCat`) is of the form `|f| t` for some
  `f : Δ[n] ⟶ A` and some `t ∈ |Δ[n]|`.  This is obtained from the tautological
  colimit-of-representables presentation of a presheaf (`Presheaf.isColimitTautologicalCocone'`)
  together with the fact that `Real` preserves colimits, and from joint surjectivity of the
  legs of a colimit cocone of types.
* `SpineTask16.coord` : the barycentric coordinates of `|Δ[n]|`, i.e. the bijection
  `|Δ[n]| ≃ stdSimplex ℝ (Fin (n.len+1))` coming from the *existing* `SSet.toTopSimplex`.
  `coord_naturality` records its compatibility with the simplicial operators.
* `SpineTask16.normalForm` (Level C, existence) : every point of `|∂Δ[r]|` is
  `|faceMap e| (coord⁻¹ v)` for a strictly monotone non-surjective `e : ⦋k⦌ ⟶ ⦋r⦌` and a point
  `v` of the *relative interior* of the standard `k`-simplex.
* `SpineTask16.standardCellMono` : `|∂Δ[r]| → |Δ[r]|` is injective, for every `r`.
* `SpineTask16.realization_skInc_injective` etc. : the Task-15 reduction is consumed, so the
  skeletal realization inclusions are unconditionally injective.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Finset

universe v w u

namespace SpineTask16

/-! ## Barycentric coordinates: support, restriction, and the induced maps -/

section Coordinates

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

open Classical in
/-- The support of a point of a standard simplex: the set of indices with positive coordinate. -/
noncomputable def supp (u : stdSimplex ℝ X) : Finset X :=
  Finset.univ.filter (fun i => 0 < u i)

lemma mem_supp {u : stdSimplex ℝ X} {i : X} : i ∈ supp u ↔ 0 < u i := by
  classical simp [supp]

lemma eq_zero_of_notMem_supp {u : stdSimplex ℝ X} {i : X} (h : i ∉ supp u) : u i = 0 :=
  ((stdSimplex.zero_le u i).lt_or_eq.resolve_left (fun hx => h (mem_supp.2 hx))).symm

/-- A point of a standard simplex has nonempty support. -/
lemma supp_nonempty (u : stdSimplex ℝ X) : (supp u).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have h1 : ∑ x, u x = 1 := stdSimplex.sum_eq_one u
  have h0 : ∑ x, u x = 0 := Finset.sum_eq_zero fun x _ => by
    rcases (stdSimplex.zero_le u x).lt_or_eq with hx | hx
    · exact absurd (mem_supp.2 hx) (by simp [h])
    · exact hx.symm
  rw [h1] at h0
  exact one_ne_zero h0

/-- The coordinates of the image of a point under the map induced by `g`. -/
lemma map_apply [DecidableEq Y] (g : X → Y) (u : stdSimplex ℝ X) (y : Y) :
    stdSimplex.map g u y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), u x := by
  show (FunOnFinite.linearMap ℝ ℝ g) (u : X → ℝ) y = _
  rw [FunOnFinite.linearMap_apply_apply]

/-- The support of the image is the image of the support. -/
lemma supp_map [DecidableEq Y] (g : X → Y) (u : stdSimplex ℝ X) :
    supp (stdSimplex.map g u) = (supp u).image g := by
  classical
  ext y
  simp only [mem_supp, Finset.mem_image, map_apply, mem_supp]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    refine absurd (Finset.sum_eq_zero (fun x hx => ?_)) h.ne'
    have hgx : g x = y := (Finset.mem_filter.1 hx).2
    rcases (stdSimplex.zero_le u x).lt_or_eq with hux | hux
    · exact absurd hgx (hc x hux)
    · exact hux.symm
  · rintro ⟨x, hx, rfl⟩
    exact lt_of_lt_of_le hx (Finset.single_le_sum (f := fun i => u i)
      (fun i _ => stdSimplex.zero_le u i) (Finset.mem_filter.2 ⟨Finset.mem_univ x, rfl⟩))

variable [DecidableEq X]

/-- Restriction of a point of a standard simplex along an injective reindexing whose image
contains the support. -/
noncomputable def restrict (g : Z → X) (hg : Function.Injective g) (u : stdSimplex ℝ X)
    (h : supp u ⊆ Finset.univ.image g) : stdSimplex ℝ Z :=
  ⟨fun z => u (g z), fun _ => stdSimplex.zero_le u _, by
    rw [← Finset.sum_image (f := fun i => u i) (g := g) (fun x _ y _ hxy => hg hxy)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans (stdSimplex.sum_eq_one u)
    intro i _ hi
    exact eq_zero_of_notMem_supp (fun hmem => hi (h hmem))⟩

@[simp] lemma restrict_apply (g : Z → X) (hg : Function.Injective g) (u : stdSimplex ℝ X)
    (h : supp u ⊆ Finset.univ.image g) (z : Z) : restrict g hg u h z = u (g z) := rfl

/-- Restriction along an injective map is a section of the induced map. -/
lemma map_restrict (g : Z → X) (hg : Function.Injective g) (u : stdSimplex ℝ X)
    (h : supp u ⊆ Finset.univ.image g) :
    stdSimplex.map g (restrict g hg u h) = u := by
  classical
  ext i
  rw [map_apply]
  simp only [restrict_apply]
  by_cases hi : ∃ z, g z = i
  · obtain ⟨z, rfl⟩ := hi
    rw [show Finset.univ.filter (fun z' => g z' = g z) = {z} by ext z'; simp [hg.eq_iff]]
    simp
  · push_neg at hi
    rw [show Finset.univ.filter (fun z => g z = i) = ∅ by ext z; simp [hi z], Finset.sum_empty]
    refine (eq_zero_of_notMem_supp (fun hmem => ?_)).symm
    obtain ⟨z, _, hz⟩ := Finset.mem_image.1 (h hmem)
    exact hi z hz

end Coordinates

/-! ## Level A: every realization point has a representative -/

instance : PreservesColimitsOfSize.{v, w} (forget TopCat.{u}) :=
  TopCat.adj₂.leftAdjoint_preservesColimits

instance : PreservesColimitsOfSize.{v, w} (SSet.toTop.{u}) :=
  sSetTopAdj.leftAdjoint_preservesColimits

/-- Geometric realization viewed as a functor to sets: the Task-15 functor `Real`. -/
noncomputable abbrev Rz : SSet.{u} ⥤ Type u := SpineTask15.Real.{u}

instance : PreservesColimitsOfSize.{v, w} (Rz.{u}) := by
  unfold Rz SpineTask15.Real; infer_instance

/-- **Level A (representative existence).**  Every point of the geometric realization of a
simplicial set `A` is the image of a point of a realized standard simplex, under the
realization of a map `Δ[n] ⟶ A`. -/
theorem exists_representative (A : SSet.{u}) (x : Rz.obj A) :
    ∃ (n : SimplexCategory) (f : SSet.stdSimplex.obj n ⟶ A)
      (t : Rz.obj (SSet.stdSimplex.obj n)), Rz.map f t = x := by
  have hc := Presheaf.isColimitTautologicalCocone'.{u} A
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (isColimitOfPreserves Rz.{u} hc) x
  exact ⟨j.left, j.hom, y, hy⟩

/-! ## Barycentric coordinates on the realization of a representable -/

/-- **Barycentric coordinates.**  The realization of the standard `n`-simplex is, as a set,
the standard topological simplex.  This uses the *existing* identification
`SSet.toTopSimplex` of the pinned library, not a new model. -/
noncomputable def coord (n : SimplexCategory) :
    Rz.{u}.obj (SSet.stdSimplex.obj n) ≃ stdSimplex ℝ (Fin (n.len + 1)) :=
  ((forget TopCat.{u}).mapIso (SSet.toTopSimplex.{u}.app n)).toEquiv.trans Equiv.ulift

/-- Naturality of barycentric coordinates in the simplex category. -/
theorem coord_naturality {n m : SimplexCategory} (a : n ⟶ m)
    (t : Rz.{u}.obj (SSet.stdSimplex.obj n)) :
    coord m (Rz.map (SSet.stdSimplex.map a) t) = stdSimplex.map a.toOrderHom (coord n t) := by
  have h := congrFun ((forget TopCat.{u}).congr_map (SSet.toTopSimplex.{u}.hom.naturality a)) t
  simp only [Functor.map_comp, types_comp_apply, Functor.comp_map] at h
  simp only [coord, Equiv.trans_apply, Functor.mapIso_hom, Iso.toEquiv_fun, Iso.app_hom,
    Functor.comp_map]
  rw [h]
  rfl

/-! ## Faces of a standard simplex, and subcomplexes of it

Everything below is stated for an arbitrary subcomplex `A ≤ Δ[r]`; the boundary `∂Δ[r]` is
the instance of interest, and its statements are recorded separately at the end. -/

variable {r k : ℕ}

/-- The simplex of `Δ[r]` corresponding to a morphism `n ⟶ ⦋r⦌`. -/
def faceSimplex {n : SimplexCategory} (e : n ⟶ ⦋r⦌) : (Δ[r] : SSet.{u}).obj (op n) :=
  SSet.stdSimplex.objEquiv.symm e

/-- The map `Δ[n] ⟶ A` attached to a morphism `e : n ⟶ ⦋r⦌` whose simplex lies in the
subcomplex `A`. -/
def subFaceMap (A : (Δ[r] : SSet.{u}).Subcomplex) {n : SimplexCategory} (e : n ⟶ ⦋r⦌)
    (hmem : faceSimplex.{u} e ∈ A.obj (op n)) : SSet.stdSimplex.obj n ⟶ (A : SSet.{u}) :=
  SSet.yonedaEquiv.symm ⟨faceSimplex e, hmem⟩

lemma subFaceMap_comp_ι (A : (Δ[r] : SSet.{u}).Subcomplex) {n : SimplexCategory} (e : n ⟶ ⦋r⦌)
    (hmem : faceSimplex.{u} e ∈ A.obj (op n)) :
    subFaceMap A e hmem ≫ A.ι = SSet.stdSimplex.map e := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map, subFaceMap, Equiv.apply_symm_apply]
  rfl

/-- The barycentric coordinates of a point of `|A|`, i.e. of its image in `|Δ[r]|`. -/
noncomputable def subCoord (A : (Δ[r] : SSet.{u}).Subcomplex) (x : Rz.{u}.obj (A : SSet.{u})) :
    stdSimplex ℝ (Fin (r + 1)) :=
  coord ⦋r⦌ (Rz.map A.ι x)

lemma subCoord_subFaceMap (A : (Δ[r] : SSet.{u}).Subcomplex) (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌)
    (hmem : faceSimplex.{u} e ∈ A.obj (op ⦋k⦌)) (v : stdSimplex ℝ (Fin (k + 1))) :
    subCoord A (Rz.map (subFaceMap A e hmem) ((coord ⦋k⦌).symm v))
      = stdSimplex.map e.toOrderHom v := by
  unfold subCoord
  rw [← types_comp_apply (Rz.map (subFaceMap A e hmem)) (Rz.map A.ι), ← Functor.map_comp,
    subFaceMap_comp_ι, coord_naturality, Equiv.apply_symm_apply]

/-- **Normal form (existence), Level C.**  Every point of the realization of a subcomplex
`A ≤ Δ[r]` is the image of an *interior* point of a realized face of `Δ[r]` that belongs to
`A`: the face is given by a strictly monotone `e : ⦋k⦌ ⟶ ⦋r⦌`, and all barycentric
coordinates of the point `v` are positive. -/
theorem subNormalForm (A : (Δ[r] : SSet.{u}).Subcomplex) (x : Rz.{u}.obj (A : SSet.{u})) :
    ∃ (k : ℕ) (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌) (hmem : faceSimplex.{u} e ∈ A.obj (op ⦋k⦌))
      (v : stdSimplex ℝ (Fin (k + 1))), StrictMono e.toOrderHom ∧ (∀ j, 0 < v j) ∧
      Rz.map (subFaceMap A e hmem) ((coord ⦋k⦌).symm v) = x := by
  obtain ⟨n, f, t, rfl⟩ := exists_representative _ x
  -- the simplex of `Δ[r]` underlying the representative; it lies in `A`
  set α : n ⟶ ⦋r⦌ := SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (f ≫ A.ι)) with hα
  have hfα : f ≫ A.ι = SSet.stdSimplex.map α := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_map, hα, Equiv.symm_apply_apply]
  have hαmem : faceSimplex.{u} α ∈ A.obj (op n) := (SSet.yonedaEquiv f).2
  -- step 1: restrict to the support of the barycentric coordinates of the representative
  set w := coord n t with hw
  obtain ⟨m, hm⟩ : ∃ m, (supp w).card = m + 1 :=
    ⟨(supp w).card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 (supp_nonempty w))).symm⟩
  set jemb := (supp w).orderEmbOfFin hm with hjemb
  set jhom : (⦋m⦌ : SimplexCategory) ⟶ n := SimplexCategory.Hom.mk ⟨jemb, jemb.monotone⟩ with hjhom
  have hsub : supp w ⊆ Finset.univ.image jemb := by rw [Finset.image_orderEmbOfFin_univ]
  set w' := restrict jemb jemb.injective w hsub with hw'
  have hw'pos : ∀ a, 0 < w' a := by
    intro a
    rw [hw', restrict_apply]
    exact mem_supp.1 (Finset.orderEmbOfFin_mem _ hm a)
  have ht : Rz.map (SSet.stdSimplex.map jhom) ((coord ⦋m⦌).symm w') = t := by
    apply (coord n).injective
    rw [coord_naturality, Equiv.apply_symm_apply]
    exact map_restrict _ _ _ _
  -- step 2: factor the resulting morphism through the increasing enumeration of its image
  set γ : (⦋m⦌ : SimplexCategory) ⟶ ⦋r⦌ := jhom ≫ α with hγ
  have hγmem : faceSimplex.{u} γ ∈ A.obj (op ⦋m⦌) := A.map jhom.op hαmem
  set S := Finset.univ.image (γ.toOrderHom : Fin (m + 1) → Fin (r + 1)) with hS
  have hmemS : ∀ a, γ.toOrderHom a ∈ S := fun a => Finset.mem_image_of_mem _ (mem_univ a)
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 :=
    ⟨S.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨_, hmemS 0⟩)).symm⟩
  set eemb := S.orderEmbOfFin hk with heemb
  set ehom : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌ := SimplexCategory.Hom.mk ⟨eemb, eemb.monotone⟩
    with hehom
  set p : Fin (m + 1) → Fin (k + 1) := fun a => (S.orderIsoOfFin hk).symm ⟨γ.toOrderHom a, hmemS a⟩
    with hp
  have hep : ∀ a, eemb (p a) = γ.toOrderHom a := by
    intro a
    rw [hp]
    exact congrArg Subtype.val ((S.orderIsoOfFin hk).apply_symm_apply ⟨γ.toOrderHom a, hmemS a⟩)
  have hpmono : Monotone p := fun a b hab =>
    eemb.le_iff_le.1 (by rw [hep, hep]; exact γ.toOrderHom.monotone hab)
  have hpsurj : Function.Surjective p := by
    intro c
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (Finset.orderEmbOfFin_mem S hk c)
    exact ⟨a, eemb.injective (by rw [hep, ha])⟩
  set phom : (⦋m⦌ : SimplexCategory) ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨p, hpmono⟩ with hphom
  have hgpe : γ = phom ≫ ehom := by
    apply SimplexCategory.Hom.ext
    ext a
    exact congrArg Fin.val (hep a).symm
  -- the face `ehom` still lies in `A`, because every epimorphism of `SimplexCategory` splits
  have hepi : Epi phom := SimplexCategory.epi_iff_surjective.2 hpsurj
  have hsplit : IsSplitEpi phom := isSplitEpi_of_epi phom
  have hsec : ehom = CategoryTheory.section_ phom ≫ γ := by
    rw [hgpe, ← Category.assoc, IsSplitEpi.id, Category.id_comp]
  have hemem : faceSimplex.{u} ehom ∈ A.obj (op ⦋k⦌) := by
    rw [hsec]
    exact A.map (CategoryTheory.section_ phom).op hγmem
  -- step 3: the resulting point is interior
  set v := stdSimplex.map p w' with hv
  have hvpos : ∀ c, 0 < v c := by
    intro c
    obtain ⟨a, rfl⟩ := hpsurj c
    rw [hv, map_apply]
    exact lt_of_lt_of_le (hw'pos a) (Finset.single_le_sum (f := fun z => w' z)
      (fun z _ => stdSimplex.zero_le w' z) (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩))
  refine ⟨k, ehom, hemem, v, eemb.strictMono, hvpos, ?_⟩
  -- step 4: the two factorisations agree, because the inclusion of `A` is a monomorphism
  have hmapeq : SSet.stdSimplex.map jhom ≫ f = SSet.stdSimplex.map phom ≫ subFaceMap A ehom hemem
      := by
    rw [← cancel_mono A.ι, Category.assoc, Category.assoc, subFaceMap_comp_ι, hfα,
      ← Functor.map_comp, ← Functor.map_comp, ← hγ, hgpe]
  have hpv : Rz.map (SSet.stdSimplex.map phom) ((coord ⦋m⦌).symm w') = (coord ⦋k⦌).symm v := by
    apply (coord ⦋k⦌).injective
    rw [coord_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  calc Rz.map (subFaceMap A ehom hemem) ((coord ⦋k⦌).symm v)
      = Rz.map (SSet.stdSimplex.map phom ≫ subFaceMap A ehom hemem) ((coord ⦋m⦌).symm w') := by
        rw [Functor.map_comp, types_comp_apply, hpv]
    _ = Rz.map (SSet.stdSimplex.map jhom ≫ f) ((coord ⦋m⦌).symm w') := by rw [hmapeq]
    _ = Rz.map f t := by rw [Functor.map_comp, types_comp_apply, ht]

/-- **Realization of the inclusion of a subcomplex of a standard simplex is injective.**
This is the general form of the standard-cell monomorphism; the boundary inclusion is the
case `A = ∂Δ[r]`. -/
theorem subcomplexMono (A : (Δ[r] : SSet.{u}).Subcomplex) :
    Function.Injective (Rz.{u}.map A.ι) := by
  intro x y hxy
  obtain ⟨k, e, hmem, v, hmono, hpos, rfl⟩ := subNormalForm A x
  obtain ⟨k', e', hmem', v', hmono', hpos', rfl⟩ := subNormalForm A y
  have hb : stdSimplex.map e.toOrderHom v = stdSimplex.map e'.toOrderHom v' := by
    rw [← subCoord_subFaceMap A e hmem v, ← subCoord_subFaceMap A e' hmem' v']
    exact congrArg (coord ⦋r⦌) hxy
  have hsuppv : supp v = Finset.univ := by ext c; simpa [mem_supp] using hpos c
  have hsuppv' : supp v' = Finset.univ := by ext c; simpa [mem_supp] using hpos' c
  have h1 : supp (stdSimplex.map e.toOrderHom v)
      = Finset.univ.image (e.toOrderHom : Fin (k + 1) → Fin (r + 1)) := by
    rw [supp_map, hsuppv]
  have h1' : supp (stdSimplex.map e'.toOrderHom v')
      = Finset.univ.image (e'.toOrderHom : Fin (k' + 1) → Fin (r + 1)) := by
    rw [supp_map, hsuppv']
  have hSS : Finset.univ.image (e.toOrderHom : Fin (k + 1) → Fin (r + 1))
      = Finset.univ.image (e'.toOrderHom : Fin (k' + 1) → Fin (r + 1)) := by
    rw [← h1, ← h1', hb]
  have hcard : k + 1 = k' + 1 := by
    have hc1 := Finset.card_image_of_injective (Finset.univ : Finset (Fin (k + 1)))
      hmono.injective
    have hc2 := Finset.card_image_of_injective (Finset.univ : Finset (Fin (k' + 1)))
      hmono'.injective
    rw [hSS, hc2] at hc1
    simpa using hc1.symm
  obtain rfl : k = k' := Nat.succ_injective hcard
  have hee : e = e' := by
    apply SimplexCategory.Hom.ext
    have hu1 := Finset.orderEmbOfFin_unique (s := Finset.univ.image
      (e.toOrderHom : Fin (k + 1) → Fin (r + 1))) (f := (e.toOrderHom : Fin (k + 1) → Fin (r + 1)))
      ((Finset.card_image_of_injective _ hmono.injective).trans (by simp))
      (fun a => Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmono
    have hu2 := Finset.orderEmbOfFin_unique (s := Finset.univ.image
      (e.toOrderHom : Fin (k + 1) → Fin (r + 1))) (f := (e'.toOrderHom : Fin (k + 1) → Fin (r + 1)))
      ((Finset.card_image_of_injective _ hmono.injective).trans (by simp))
      (fun a => hSS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmono'
    ext a
    exact congrArg Fin.val (congrFun (hu1.trans hu2.symm) a)
  subst hee
  have hvv : v = v' := by
    ext c
    have h := congrArg (fun z => (z : stdSimplex ℝ (Fin (r + 1))) (e.toOrderHom c)) hb
    simp only [map_apply] at h
    rw [show Finset.univ.filter (fun a => e.toOrderHom a = e.toOrderHom c) = {c} by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hmono.injective h, fun h => by rw [h]⟩] at h
    simpa using h
  rw [hvv]

/-! ## The standard cell: the boundary inclusion -/

/-- The map `Δ[k] ⟶ ∂Δ[r]` attached to a non-surjective morphism `e : ⦋k⦌ ⟶ ⦋r⦌`.  (Membership
of the corresponding simplex in `∂Δ[r]` *is* non-surjectivity.) -/
def faceMap (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌) (hns : ¬ Function.Surjective e.toOrderHom) :
    (Δ[k] : SSet.{u}) ⟶ ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u}) :=
  subFaceMap (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) e hns

lemma faceMap_comp_ι (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌)
    (hns : ¬ Function.Surjective e.toOrderHom) :
    faceMap.{u} e hns ≫ (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι = SSet.stdSimplex.map e :=
  subFaceMap_comp_ι (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) e hns

/-- The barycentric coordinates of a point of `|∂Δ[r]|`, i.e. of its image in `|Δ[r]|`. -/
noncomputable def bdCoord (r : ℕ)
    (x : Rz.{u}.obj ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u})) :
    stdSimplex ℝ (Fin (r + 1)) :=
  subCoord (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) x

lemma bdCoord_faceMap (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌)
    (hns : ¬ Function.Surjective e.toOrderHom) (v : stdSimplex ℝ (Fin (k + 1))) :
    bdCoord.{u} r (Rz.map (faceMap e hns) ((coord ⦋k⦌).symm v))
      = stdSimplex.map e.toOrderHom v :=
  subCoord_subFaceMap (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) e hns v

/-- **Normal form (existence) for the standard boundary.**  Every point of `|∂Δ[r]|` is the
image of an interior point of a realized proper face. -/
theorem normalForm (r : ℕ)
    (x : Rz.{u}.obj ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u})) :
    ∃ (k : ℕ) (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌) (hns : ¬ Function.Surjective e.toOrderHom)
      (v : stdSimplex ℝ (Fin (k + 1))), StrictMono e.toOrderHom ∧ (∀ j, 0 < v j) ∧
      Rz.map (faceMap e hns) ((coord ⦋k⦌).symm v) = x :=
  subNormalForm (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) x

/-- **WP6, the main theorem.**  The geometric realization of the boundary inclusion of the
standard `r`-simplex is injective. -/
theorem standardCellMono (r : ℕ) : SpineTask15.StandardCellMono.{u} r :=
  subcomplexMono (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)

end SpineTask16
