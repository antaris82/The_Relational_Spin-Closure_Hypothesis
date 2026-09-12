import RequestProject.Spine.Nerve.Geometry.PointModel

/-!
# The normal form of a point of a geometric realization

Every point of `|K|` is `|σ|(u)` for a **unique** pair consisting of a nondegenerate simplex
`σ` of `K` and an interior point `u` of the topological simplex of the same dimension.  This is
the point model of the realization (Milnor's lemma); the pinned library has no such statement.

The uniqueness is what makes the realization behave like a CW complex, and it is what the
skeletal factorization of a singular simplex ultimately rests on.

## Contents

* `cellPoint a w` — the point of `|K|` determined by a simplex `a` and barycentric coordinates
  `w`, and `cellPoint_map`, its behaviour under a simplicial operator;
* `exists_face_interior` — a point of a topological simplex is an interior point of a unique
  face (`face_len_unique`, `face_unique`);
* `IsNF a w p` — the predicate "the normal form of `cellPoint a w` is `p`", where a *normal
  form* `p : NFData K` is a nondegenerate simplex of `K` together with its (extended)
  barycentric coordinates; `isNF_exists` and `isNF_unique`;
* `nfOf a w` — the normal form of `(a, w)`, and `isNF_map`, its invariance under simplicial
  operators;
* `nf x` — **the normal form of an arbitrary point of `|K|`**, obtained from the tautological
  colimit presentation of `K` by realizations of standard simplices, with
  `nf_cellPoint : nf (cellPoint a w) = nfOf a w`;
* `cellPoint_injective_of_nondegenerate` and `carrierDim` — the consequences actually used:
  the dimension of the carrier of a point is well defined, and a point determines the
  nondegenerate simplex and interior coordinates it comes from.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Finset SpineTask16

universe u

namespace NerveNormalForm

variable {K : SSet.{u}}

/-! ## Points of the realization coming from a simplex -/

/-- The point of `|K|` determined by a simplex `a` and barycentric coordinates `w`. -/
noncomputable def cellPoint {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) : Rz.{u}.obj K :=
  Rz.map (SSet.yonedaEquiv.symm a) ((coord X).symm w)

theorem yonedaEquiv_symm_map {X Y : SimplexCategory} (a : K.obj (op X)) (α : Y ⟶ X) :
    SSet.yonedaEquiv.symm (K.map α.op a) = SSet.stdSimplex.map α ≫ SSet.yonedaEquiv.symm a := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map, Equiv.apply_symm_apply]
  show _ = (SSet.yonedaEquiv.symm a).app (op Y) (SSet.stdSimplex.objEquiv.symm α)
  rw [← Equiv.apply_symm_apply SSet.yonedaEquiv a]
  rfl

theorem coord_symm_map {X Y : SimplexCategory} (α : Y ⟶ X) (w : stdSimplex ℝ (Fin (Y.len + 1))) :
    Rz.map (SSet.stdSimplex.map α) ((coord Y).symm w)
      = (coord X).symm (stdSimplex.map α.toOrderHom w) := by
  apply (coord X).injective
  rw [coord_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- A simplicial operator can be moved from the simplex to the coordinates. -/
theorem cellPoint_map {X Y : SimplexCategory} (a : K.obj (op X)) (α : Y ⟶ X)
    (w : stdSimplex ℝ (Fin (Y.len + 1))) :
    cellPoint (K.map α.op a) w = cellPoint a (stdSimplex.map α.toOrderHom w) := by
  unfold cellPoint
  rw [yonedaEquiv_symm_map, Functor.map_comp, types_comp_apply, coord_symm_map]

/-! ## The face carrying a point of a topological simplex -/

theorem supp_eq_univ_of_pos {n : ℕ} {v : stdSimplex ℝ (Fin (n + 1))} (hv : ∀ j, 0 < v j) :
    supp v = Finset.univ := Finset.eq_univ_iff_forall.2 (fun j => mem_supp.2 (hv j))

theorem supp_map_interior {X : SimplexCategory} {k : ℕ} (e : (⦋k⦌ : SimplexCategory) ⟶ X)
    {v : stdSimplex ℝ (Fin (k + 1))} (hv : ∀ j, 0 < v j) :
    supp (stdSimplex.map e.toOrderHom v) = Finset.univ.image e.toOrderHom := by
  rw [supp_map, supp_eq_univ_of_pos hv]

/-- The coordinate of an interior point is recovered from its image on the face. -/
theorem map_apply_of_injective {X : SimplexCategory} {k : ℕ}
    (e : (⦋k⦌ : SimplexCategory) ⟶ X) (he : Function.Injective e.toOrderHom)
    (v : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1)) :
    stdSimplex.map e.toOrderHom v (e.toOrderHom j) = v j := by
  classical
  rw [map_apply, show Finset.univ.filter (fun x => e.toOrderHom x = e.toOrderHom j) = {j} by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact he.eq_iff]
  simp

/-- Two faces carrying the same point in their interior have the same dimension. -/
theorem face_len_unique {X : SimplexCategory} {k k' : ℕ} (e : (⦋k⦌ : SimplexCategory) ⟶ X)
    (e' : (⦋k'⦌ : SimplexCategory) ⟶ X)
    (he : Function.Injective e.toOrderHom) (he' : Function.Injective e'.toOrderHom)
    {v : stdSimplex ℝ (Fin (k + 1))} {v' : stdSimplex ℝ (Fin (k' + 1))}
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j)
    (h : stdSimplex.map e.toOrderHom v = stdSimplex.map e'.toOrderHom v') : k = k' := by
  have h1 : (Finset.univ.image e.toOrderHom).card = (Finset.univ.image e'.toOrderHom).card := by
    rw [← supp_map_interior e hv, ← supp_map_interior e' hv', h]
  rw [Finset.card_image_of_injective _ he, Finset.card_image_of_injective _ he'] at h1
  simpa using h1

/-- **A point of a topological simplex lies in the interior of a unique face.** -/
theorem face_unique {X : SimplexCategory} {k : ℕ} (e e' : (⦋k⦌ : SimplexCategory) ⟶ X)
    (he : Function.Injective e.toOrderHom) (he' : Function.Injective e'.toOrderHom)
    {v v' : stdSimplex ℝ (Fin (k + 1))}
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j)
    (h : stdSimplex.map e.toOrderHom v = stdSimplex.map e'.toOrderHom v') :
    e = e' ∧ v = v' := by
  classical
  set S := supp (stdSimplex.map e.toOrderHom v) with hS
  have hcard : S.card = k + 1 := by
    rw [hS, supp_map_interior e hv, Finset.card_image_of_injective _ he]
    simp
  have hmem : ∀ x, e.toOrderHom x ∈ S := by
    intro x
    rw [hS, supp_map_interior e hv]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
  have hmem' : ∀ x, e'.toOrderHom x ∈ S := by
    intro x
    rw [hS, h, supp_map_interior e' hv']
    exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
  have hsm : StrictMono (e.toOrderHom : Fin (k + 1) → Fin (X.len + 1)) :=
    (e.toOrderHom.monotone).strictMono_of_injective he
  have hsm' : StrictMono (e'.toOrderHom : Fin (k + 1) → Fin (X.len + 1)) :=
    (e'.toOrderHom.monotone).strictMono_of_injective he'
  have hee : (e.toOrderHom : Fin (k + 1) → Fin (X.len + 1)) = e'.toOrderHom := by
    rw [Finset.orderEmbOfFin_unique hcard hmem hsm, Finset.orderEmbOfFin_unique hcard hmem' hsm']
  refine ⟨SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ hee), ?_⟩
  ext j
  rw [← map_apply_of_injective e he v j, ← map_apply_of_injective e' he' v' j, h, hee]

/-- Existence of the carrying face. -/
theorem exists_face_interior {X : SimplexCategory} (w : stdSimplex ℝ (Fin (X.len + 1))) :
    ∃ (k : ℕ) (e : (⦋k⦌ : SimplexCategory) ⟶ X) (v : stdSimplex ℝ (Fin (k + 1))),
      Function.Injective e.toOrderHom ∧ (∀ j, 0 < v j) ∧
        stdSimplex.map e.toOrderHom v = w := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, (supp w).card = m + 1 :=
    ⟨(supp w).card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 (supp_nonempty w))).symm⟩
  set jemb := (supp w).orderEmbOfFin hm with hjemb
  set jhom : (⦋m⦌ : SimplexCategory) ⟶ X := SimplexCategory.Hom.mk ⟨jemb, jemb.monotone⟩ with hjhom
  have hsub : supp w ⊆ Finset.univ.image jemb := by rw [Finset.image_orderEmbOfFin_univ]
  refine ⟨m, jhom, restrict jemb jemb.injective w hsub, jemb.injective, ?_, ?_⟩
  · intro a
    rw [restrict_apply]
    exact mem_supp.1 (Finset.orderEmbOfFin_mem _ hm a)
  · exact map_restrict _ _ _ _

/-! ## Normal-form data -/

/-- Normal-form data for a point of `|K|`: a nondegenerate simplex, and the barycentric
coordinates of the point in the corresponding cell, extended by zero to a function on `ℕ` so
that the type does not depend on the dimension. -/
abbrev NFData (K : SSet.{u}) : Type u := K.N × (ℕ → ℝ)

/-- Barycentric coordinates, extended by zero. -/
def extend {n : ℕ} (v : stdSimplex ℝ (Fin (n + 1))) : ℕ → ℝ :=
  fun i => if h : i < n + 1 then v ⟨i, h⟩ else 0

theorem extend_injective {n : ℕ} {v v' : stdSimplex ℝ (Fin (n + 1))} (h : extend v = extend v') :
    v = v' := by
  ext j
  have := congrFun h j.1
  simpa [extend, j.2] using this

/-- The predicate defining the normal form of the point `cellPoint a w`. -/
def IsNF {X : SimplexCategory} (a : K.obj (op X)) (w : stdSimplex ℝ (Fin (X.len + 1)))
    (p : NFData K) : Prop :=
  ∃ (k m : ℕ) (e : (⦋k⦌ : SimplexCategory) ⟶ X) (φ : (⦋k⦌ : SimplexCategory) ⟶ ⦋m⦌)
      (v : stdSimplex ℝ (Fin (k + 1))) (σ : K _⦋m⦌) (hσ : σ ∈ K.nonDegenerate m),
    Function.Injective e.toOrderHom ∧ Epi φ ∧ (∀ j, 0 < v j) ∧
      stdSimplex.map e.toOrderHom v = w ∧ K.map e.op a = K.map φ.op σ ∧
      p = (SSet.N.mk σ hσ, extend (stdSimplex.map φ.toOrderHom v))

theorem isNF_exists {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) : ∃ p, IsNF a w p := by
  obtain ⟨k, e, v, he, hv, hw⟩ := exists_face_interior w
  obtain ⟨m, φ, hφ, ⟨σ, hσ⟩, hb⟩ := K.exists_nonDegenerate (n := k) (K.map e.op a)
  exact ⟨_, k, m, e, φ, v, σ, hσ, he, hφ, hv, hw, hb, rfl⟩

/-- The Eilenberg–Zilber uniqueness, in the form needed here. -/
theorem ez_unique {k m m' : ℕ} (b : K _⦋k⦌)
    (φ : (⦋k⦌ : SimplexCategory) ⟶ ⦋m⦌) (φ' : (⦋k⦌ : SimplexCategory) ⟶ ⦋m'⦌)
    [Epi φ] [Epi φ'] (σ : K _⦋m⦌) (σ' : K _⦋m'⦌)
    (hσ : σ ∈ K.nonDegenerate m) (hσ' : σ' ∈ K.nonDegenerate m')
    (h : b = K.map φ.op σ) (h' : b = K.map φ'.op σ') :
    ∃ _ : m = m', HEq φ φ' ∧ HEq σ σ' := by
  have hm : m = m' := K.unique_nonDegenerate_dim b φ ⟨σ, hσ⟩ h φ' ⟨σ', hσ'⟩ h'
  subst hm
  have h1 : (⟨σ, hσ⟩ : K.nonDegenerate m) = ⟨σ', hσ'⟩ :=
    K.unique_nonDegenerate_simplex b φ ⟨σ, hσ⟩ h φ' ⟨σ', hσ'⟩ h'
  have h2 : φ = φ' := K.unique_nonDegenerate_map b φ ⟨σ, hσ⟩ h φ' ⟨σ', hσ'⟩ h'
  exact ⟨rfl, heq_of_eq h2, heq_of_eq (congrArg Subtype.val h1)⟩

/-- **The normal form is unique.** -/
theorem isNF_unique {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) {p p' : NFData K}
    (h : IsNF a w p) (h' : IsNF a w p') : p = p' := by
  obtain ⟨k, m, e, φ, v, σ, hσ, he, hφ, hv, hw, hb, hp⟩ := h
  obtain ⟨k', m', e', φ', v', σ', hσ', he', hφ', hv', hw', hb', hp'⟩ := h'
  have hk : k = k' := face_len_unique e e' he he' hv hv' (by rw [hw, hw'])
  subst hk
  obtain ⟨hee, hvv⟩ := face_unique e e' he he' hv hv' (by rw [hw, hw'])
  subst hee
  subst hvv
  haveI := hφ
  haveI := hφ'
  obtain ⟨hmm, hφφ, hσσ⟩ := ez_unique (K.map e.op a) φ φ' σ σ' hσ hσ' hb hb'
  subst hmm
  obtain rfl : φ = φ' := eq_of_heq hφφ
  obtain rfl : σ = σ' := eq_of_heq hσσ
  rw [hp, hp']

/-! ## Naturality of the normal form -/

/-- Every simplicial operator factors as an epimorphism followed by a monomorphism. -/
theorem exists_epi_mono_factorisation {Y X : SimplexCategory} (γ : Y ⟶ X) :
    ∃ (k : ℕ) (ψ : Y ⟶ ⦋k⦌) (e : (⦋k⦌ : SimplexCategory) ⟶ X), Epi ψ ∧ Mono e ∧ ψ ≫ e = γ :=
  ⟨(Limits.image γ).len, Limits.factorThruImage γ, Limits.image.ι γ,
    inferInstance, inferInstance, Limits.image.fac γ⟩

theorem toOrderHom_comp {X Y Z : SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).toOrderHom : _ → _) = g.toOrderHom ∘ f.toOrderHom := rfl

/-- The image of an interior point under a surjective reindexing is interior. -/
theorem map_pos_of_surjective {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {g : X → Y} (hg : Function.Surjective g) {v : stdSimplex ℝ X} (hv : ∀ i, 0 < v i)
    (j : Y) : 0 < stdSimplex.map g v j := by
  obtain ⟨i, rfl⟩ := hg j
  rw [map_apply]
  exact lt_of_lt_of_le (hv i) (Finset.single_le_sum (f := fun z => v z)
    (fun z _ => stdSimplex.zero_le v z) (Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩))

theorem presheaf_map_comp {X Y Z : SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) (x : K.obj (op Z)) :
    K.map (f ≫ g).op x = K.map f.op (K.map g.op x) := by
  rw [op_comp, K.map_comp, types_comp_apply]

theorem yonedaEquiv_map {X Y : SimplexCategory} (g : SSet.stdSimplex.obj X ⟶ K) (α : Y ⟶ X) :
    SSet.yonedaEquiv (SSet.stdSimplex.map α ≫ g) = K.map α.op (SSet.yonedaEquiv g) := by
  have h := yonedaEquiv_symm_map (K := K) (SSet.yonedaEquiv g) α
  rw [Equiv.symm_apply_apply] at h
  simpa using (congrArg SSet.yonedaEquiv h).symm

/-- **The normal form is natural**: moving a simplicial operator from the simplex to the
coordinates does not change the normal form. -/
theorem isNF_map {X Y : SimplexCategory} (a : K.obj (op X)) (α : Y ⟶ X)
    (w : stdSimplex ℝ (Fin (Y.len + 1))) {p : NFData K}
    (h : IsNF (K.map α.op a) w p) : IsNF a (stdSimplex.map α.toOrderHom w) p := by
  obtain ⟨k, m, e, φ, v, σ, hσ, he, hφ, hv, hw, hb, hp⟩ := h
  obtain ⟨k', ψ, e', hψ, he', hfac⟩ := exists_epi_mono_factorisation (e ≫ α)
  haveI := hψ; haveI := he'; haveI := hφ
  have hψs : Function.Surjective ψ.toOrderHom := SimplexCategory.epi_iff_surjective.1 hψ
  have he'i : Function.Injective e'.toOrderHom := SimplexCategory.mono_iff_injective.1 he'
  set v' := stdSimplex.map ψ.toOrderHom v with hv'
  have hv'pos : ∀ j, 0 < v' j := fun j => map_pos_of_surjective hψs hv j
  have hw' : stdSimplex.map e'.toOrderHom v' = stdSimplex.map α.toOrderHom w := by
    rw [hv', stdSimplex.map_comp_apply, ← toOrderHom_comp, hfac, toOrderHom_comp,
      ← stdSimplex.map_comp_apply, hw]
  obtain ⟨m', φ'', hφ'', ⟨σ', hσ'⟩, hb'⟩ := K.exists_nonDegenerate (n := k') (K.map e'.op a)
  haveI := hφ''
  have key : K.map φ.op σ = K.map (ψ ≫ φ'').op σ' := by
    rw [presheaf_map_comp, ← hb', ← presheaf_map_comp, hfac, presheaf_map_comp, ← hb]
  obtain ⟨hmm, hφφ, hσσ⟩ := ez_unique (K.map φ.op σ) φ (ψ ≫ φ'') σ σ' hσ hσ' rfl key
  subst hmm
  obtain rfl : φ = ψ ≫ φ'' := eq_of_heq hφφ
  obtain rfl : σ = σ' := eq_of_heq hσσ
  refine ⟨k', m, e', φ'', v', σ, hσ, he'i, hφ'', hv'pos, hw', hb', ?_⟩
  rw [hp, hv', toOrderHom_comp, ← stdSimplex.map_comp_apply]

/-! ## The normal form as a function -/

/-- The normal form of the pair `(a, w)`. -/
noncomputable def nfOf {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) : NFData K := (isNF_exists a w).choose

theorem isNF_nfOf {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) : IsNF a w (nfOf a w) := (isNF_exists a w).choose_spec

theorem nfOf_eq {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) {p : NFData K} (h : IsNF a w p) : nfOf a w = p :=
  isNF_unique a w (isNF_nfOf a w) h

theorem nfOf_map {X Y : SimplexCategory} (a : K.obj (op X)) (α : Y ⟶ X)
    (w : stdSimplex ℝ (Fin (Y.len + 1))) :
    nfOf a (stdSimplex.map α.toOrderHom w) = nfOf (K.map α.op a) w :=
  nfOf_eq _ _ (isNF_map a α w (isNF_nfOf _ _))

/-- The cocone of normal-form data over the tautological presentation of `K` by standard
simplices. -/
noncomputable def nfCocone (K : SSet.{u}) :
    Cocone ((CostructuredArrow.proj uliftYoneda.{u, 0, 0} K ⋙ uliftYoneda.{u, 0, 0}) ⋙ Rz.{u})
    where
  pt := NFData K
  ι :=
    { app := fun j t => nfOf (SSet.yonedaEquiv j.hom) (coord j.left t)
      naturality := by
        intro j j' f
        funext t
        show nfOf (SSet.yonedaEquiv j'.hom)
              (coord j'.left (Rz.map (SSet.stdSimplex.map f.left) t))
            = nfOf (SSet.yonedaEquiv j.hom) (coord j.left t)
        rw [coord_naturality, nfOf_map, ← yonedaEquiv_map]
        congr 2
        exact CostructuredArrow.w f }

/-- **The normal form of an arbitrary point of `|K|`.** -/
noncomputable def nf (K : SSet.{u}) : Rz.{u}.obj K → NFData K :=
  (isColimitOfPreserves Rz.{u} (Presheaf.isColimitTautologicalCocone'.{u} K)).desc (nfCocone K)

@[simp] theorem nf_cellPoint {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) : nf K (cellPoint a w) = nfOf a w := by
  have h := (isColimitOfPreserves Rz.{u} (Presheaf.isColimitTautologicalCocone'.{u} K)).fac
    (nfCocone K) (CostructuredArrow.mk (SSet.yonedaEquiv.symm a))
  have h2 := congrFun h ((coord X).symm w)
  simpa [cellPoint, nf, nfCocone] using h2

/-! ## The carrier of a point -/

/-- **Every point of `|K|` is an interior point of the cell of a unique nondegenerate simplex.**
Existence, together with the fact that the normal form computes it. -/
theorem exists_cellPoint_nf (K : SSet.{u}) (x : Rz.{u}.obj K) :
    ∃ (m : ℕ) (σ : K _⦋m⦌) (hσ : σ ∈ K.nonDegenerate m) (u : stdSimplex ℝ (Fin (m + 1))),
      (∀ j, 0 < u j) ∧ nf K x = (SSet.N.mk σ hσ, extend u) ∧ cellPoint σ u = x := by
  obtain ⟨X, f, t, rfl⟩ := exists_representative K x
  set a := SSet.yonedaEquiv f with ha
  set w := coord X t with hw
  have hx : cellPoint a w = Rz.map f t := by
    rw [cellPoint, ha, Equiv.symm_apply_apply, hw, Equiv.symm_apply_apply]
  obtain ⟨k, m, e, φ, v, σ, hσ, he, hφ, hv, hwe, hb, hp⟩ := isNF_nfOf a w
  haveI := hφ
  refine ⟨m, σ, hσ, stdSimplex.map φ.toOrderHom v,
    fun j => map_pos_of_surjective (SimplexCategory.epi_iff_surjective.1 hφ) hv j, ?_, ?_⟩
  · rw [← hx, nf_cellPoint, hp]
  · rw [← cellPoint_map, ← hb, cellPoint_map, hwe, hx]

/-- The dimension of the carrier of a point of `|K|`. -/
noncomputable def carrierDim (K : SSet.{u}) (x : Rz.{u}.obj K) : ℕ := (nf K x).1.dim

end NerveNormalForm
