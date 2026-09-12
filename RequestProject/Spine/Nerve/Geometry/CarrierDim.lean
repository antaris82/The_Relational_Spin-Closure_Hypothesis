import RequestProject.Spine.Nerve.Geometry.NormalForm

/-!
# The carrier of a point of a realization, and the realized subcomplexes

The normal form of `Nerve/Geometry/NormalForm.lean` attaches to every point `x` of `|K|` a
nondegenerate simplex of `K` — its *carrier* — together with an interior point of the
corresponding topological simplex.  This module records the consequence that matters for the
skeletal filtration:

* `NerveNormalForm.mem_range_subcomplex_iff` — a point of `|K|` lies in the image of the
  realization of a subcomplex `A ≤ K` **iff** its carrier is a simplex of `A`;
* `NerveNormalForm.mem_range_skeleton_iff` — specialised to the skeleta: the image of
  `|Sk K r| → |K|` is exactly the set of points of carrier dimension `< r`.

Nothing here is topological; these are statements about the underlying sets.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Finset SpineTask16

universe u

namespace NerveNormalForm

variable {K : SSet.{u}}

/-! ## Cell points and maps of simplicial sets -/

/-- Cell points are natural in the simplicial set. -/
theorem cellPoint_naturality {L K : SSet.{u}} (g : L ⟶ K) {X : SimplexCategory}
    (a : L.obj (op X)) (w : stdSimplex ℝ (Fin (X.len + 1))) :
    Rz.map g (cellPoint a w) = cellPoint (g.app (op X) a) w := by
  have hg : SSet.yonedaEquiv.symm a ≫ g = SSet.yonedaEquiv.symm (g.app (op X) a) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  unfold cellPoint
  rw [← types_comp_apply (Rz.map _) (Rz.map g), ← Functor.map_comp, hg]

/-- The normal form of an interior point of the cell of a nondegenerate simplex is that
simplex together with the coordinates of the point. -/
theorem nfOf_nondegenerate {m : ℕ} (σ : K _⦋m⦌) (hσ : σ ∈ K.nonDegenerate m)
    (u : stdSimplex ℝ (Fin (m + 1))) (hu : ∀ j, 0 < u j) :
    nfOf σ u = (SSet.N.mk σ hσ, extend u) := by
  refine nfOf_eq _ _ ⟨m, m, 𝟙 _, 𝟙 _, u, σ, hσ, fun a b h => h, inferInstance, hu, ?_, ?_, ?_⟩
  · show stdSimplex.map id u = u
    exact stdSimplex.map_id_apply u
  · simp
  · congr 1
    show extend u = extend (stdSimplex.map id u)
    rw [stdSimplex.map_id_apply u]

theorem nf_cellPoint_nondegenerate {m : ℕ} (σ : K _⦋m⦌) (hσ : σ ∈ K.nonDegenerate m)
    (u : stdSimplex ℝ (Fin (m + 1))) (hu : ∀ j, 0 < u j) :
    nf K (cellPoint σ u) = (SSet.N.mk σ hσ, extend u) := by
  rw [nf_cellPoint, nfOf_nondegenerate σ hσ u hu]

/-- Two nondegenerate simplices of the same dimension defining the same element of `K.N` are
equal. -/
theorem N_mk_inj {m : ℕ} {σ σ' : K _⦋m⦌} {hσ : σ ∈ K.nonDegenerate m}
    {hσ' : σ' ∈ K.nonDegenerate m} (h : SSet.N.mk σ hσ = SSet.N.mk σ' hσ') : σ = σ' := by
  have h2 : (SSet.S.mk σ : K.S) = SSet.S.mk σ' := (SSet.N.ext_iff _ _).1 h
  simpa using h2

/-- **The normal form determines the point**: `nf` is injective. -/
theorem nf_injective (K : SSet.{u}) : Function.Injective (nf K) := by
  intro x x' h
  obtain ⟨m, σ, hσ, u, hu, hnf, hx⟩ := exists_cellPoint_nf K x
  obtain ⟨m', σ', hσ', u', hu', hnf', hx'⟩ := exists_cellPoint_nf K x'
  rw [hnf, hnf'] at h
  have hdim : m = m' := congrArg (fun p => (p : NFData K).1.dim) h
  subst hdim
  have h1 : SSet.N.mk σ hσ = SSet.N.mk σ' hσ' := congrArg Prod.fst h
  have h2 : extend u = extend u' := congrArg Prod.snd h
  rw [← hx, ← hx', N_mk_inj h1, extend_injective h2]

/-! ## Subcomplexes -/

/-- A nondegenerate simplex of a subcomplex is nondegenerate in the ambient simplicial set. -/
theorem nonDegenerate_of_subcomplex (A : K.Subcomplex) {n : ℕ} (τ : (A : SSet.{u}) _⦋n⦌)
    (hτ : τ ∈ (A : SSet.{u}).nonDegenerate n) : (τ : K _⦋n⦌) ∈ K.nonDegenerate n := by
  intro hdeg
  rw [SSet.mem_degenerate_iff] at hdeg
  obtain ⟨m, hm, f, hf, z, hz⟩ := hdeg
  haveI := hf
  haveI : IsSplitEpi f := isSplitEpi_of_epi f
  have hzeq : K.map (CategoryTheory.section_ f).op (τ : K _⦋n⦌) = z := by
    rw [← hz, ← presheaf_map_comp, IsSplitEpi.id, op_id, K.map_id, types_id_apply]
  have hzmem : z ∈ A.obj (op ⦋m⦌) := by
    rw [← hzeq]; exact A.map _ τ.2
  exact hτ ⟨m, hm, f, ⟨⟨z, hzmem⟩, Subtype.ext hz⟩⟩

/-- The predicate "the nondegenerate simplex `s` belongs to the subcomplex `A`", as a predicate
on `K.N`; phrasing it this way avoids all dependent-type juggling. -/
def SimplexMem (A : K.Subcomplex) (s : K.N) : Prop := s.simplex ∈ A.obj (op ⦋s.dim⦌)

theorem simplexMem_mk (A : K.Subcomplex) {m : ℕ} (σ : K _⦋m⦌) (hσ : σ ∈ K.nonDegenerate m) :
    SimplexMem A (SSet.N.mk σ hσ) ↔ σ ∈ A.obj (op ⦋m⦌) := Iff.rfl

/-- Any cell point of a simplex of `A` lies in the image of `|A| → |K|`. -/
theorem mem_range_of_simplex_mem (A : K.Subcomplex) {m : ℕ} {σ : K _⦋m⦌}
    (hmem : σ ∈ A.obj (op ⦋m⦌)) (u : stdSimplex ℝ (Fin (m + 1))) :
    cellPoint σ u ∈ Set.range (Rz.{u}.map A.ι) :=
  ⟨cellPoint (X := ⦋m⦌) (⟨σ, hmem⟩ : (A : SSet.{u}) _⦋m⦌) u,
    (cellPoint_naturality (X := ⦋m⦌) A.ι _ u).trans rfl⟩

/-- **The image of the realization of a subcomplex.**  A point of `|K|` lies in the image of
`|A| → |K|` if and only if its carrier is a simplex of `A`. -/
theorem mem_range_subcomplex_iff (A : K.Subcomplex) (x : Rz.{u}.obj K) :
    x ∈ Set.range (Rz.{u}.map A.ι) ↔ SimplexMem A (nf K x).1 := by
  obtain ⟨m, σ, hσ, u, hu, hnf, hx⟩ := exists_cellPoint_nf K x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨m', τ, hτ, u', hu', -, hy⟩ := exists_cellPoint_nf (A : SSet.{u}) y
    have hxy : cellPoint (τ : K _⦋m'⦌) u' = Rz.map A.ι y := by
      rw [← hy, cellPoint_naturality]
      rfl
    have hnd : (τ : K _⦋m'⦌) ∈ K.nonDegenerate m' := nonDegenerate_of_subcomplex A τ hτ
    have : nf K (Rz.map A.ι y) = (SSet.N.mk (τ : K _⦋m'⦌) hnd, extend u') := by
      rw [← hxy, nf_cellPoint_nondegenerate _ hnd u' hu']
    rw [this]
    exact τ.2
  · intro hmem
    rw [hnf] at hmem
    rw [← hx]
    exact mem_range_of_simplex_mem A ((simplexMem_mk A σ hσ).1 hmem) u

/-- **The realization of a subcomplex injects into the realization**, for an arbitrary
subcomplex of an arbitrary simplicial set. -/
theorem realization_subcomplex_injective (A : K.Subcomplex) :
    Function.Injective (Rz.{u}.map A.ι) := by
  intro y y' h
  obtain ⟨m, τ, hτ, u, hu, -, hy⟩ := exists_cellPoint_nf (A : SSet.{u}) y
  obtain ⟨m', τ', hτ', u', hu', -, hy'⟩ := exists_cellPoint_nf (A : SSet.{u}) y'
  have e1 : Rz.{u}.map A.ι y = cellPoint (τ : K _⦋m⦌) u := by
    rw [← hy, cellPoint_naturality]; rfl
  have e2 : Rz.{u}.map A.ι y' = cellPoint (τ' : K _⦋m'⦌) u' := by
    rw [← hy', cellPoint_naturality]; rfl
  have hnd := nonDegenerate_of_subcomplex A τ hτ
  have hnd' := nonDegenerate_of_subcomplex A τ' hτ'
  have hnf : nf K (cellPoint (τ : K _⦋m⦌) u) = nf K (cellPoint (τ' : K _⦋m'⦌) u') := by
    rw [← e1, ← e2, h]
  rw [nf_cellPoint_nondegenerate _ hnd u hu, nf_cellPoint_nondegenerate _ hnd' u' hu'] at hnf
  have hdim : m = m' := congrArg (fun p => (p : NFData K).1.dim) hnf
  subst hdim
  have h1 : SSet.N.mk (τ : K _⦋m⦌) hnd = SSet.N.mk (τ' : K _⦋m⦌) hnd' := congrArg Prod.fst hnf
  have h2 : extend u = extend u' := congrArg Prod.snd hnf
  rw [← hy, ← hy', Subtype.ext (N_mk_inj h1), extend_injective h2]

/-! ## The skeletal filtration -/

/-- **The image of the realization of a skeleton** is exactly the set of points of carrier
dimension `< r`. -/
theorem mem_range_skeleton_iff (K : SSet.{u}) (r : ℕ) (x : Rz.{u}.obj K) :
    x ∈ Set.range (Rz.{u}.map (K.skeleton r).ι) ↔ carrierDim K x < r := by
  rw [mem_range_subcomplex_iff]
  exact SSet.mem_skeleton_obj_iff_of_nonDegenerate
    (x := ⟨(nf K x).1.simplex, (nf K x).1.nonDegenerate⟩) (n := r)

end NerveNormalForm
