import RequestProject.Spine.Nerve.Geometry.RealizationTopology

/-!
# Realized subcomplexes are closed subspaces, and compact domains factor through a skeleton

Two consequences of the weak topology of `|K|` and of the point model:

* `NerveTopology.isClosedMap_realization_subcomplex` — for **any** subcomplex `A ≤ K`, the
  realization `|A| → |K|` is a closed map; since it is also injective, `|A|` is a closed
  subspace of `|K|`;
* `NerveTopology.exists_skeletal_factorization` — **a continuous map from a compact space into
  `|K|` factors continuously through some `|Sk K r|`.**

The second statement is the exact topological input needed to pass from the skeletal comparison
isomorphisms to the global one.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Finset SpineTask16 NerveNormalForm

universe u v

namespace NerveTopology

variable {K : SSet.{u}}

/-! ## Realized subcomplexes are closed -/

/-- **The realization of a subcomplex inclusion is a closed map.** -/
theorem isClosedMap_realization_subcomplex (A : K.Subcomplex) :
    IsClosedMap (realMap A.ι) := by
  classical
  intro S hS
  rw [isClosed_iff]
  intro X a
  set C : (Σ (k : Fin (X.len + 1)), ((⦋(k : ℕ)⦌ : SimplexCategory) ⟶ X)) →
      Set (stdSimplex ℝ (Fin (X.len + 1))) :=
    fun i => if h : K.map i.2.op a ∈ A.obj (op ⦋(i.1 : ℕ)⦌) then
        (stdSimplex.map i.2.toOrderHom) ''
          {v | cellPoint (X := ⦋(i.1 : ℕ)⦌)
            (⟨K.map i.2.op a, h⟩ : (A : SSet.{u}) _⦋(i.1 : ℕ)⦌) v ∈ S}
      else ∅ with hC
  have hcov : {w : stdSimplex ℝ (Fin (X.len + 1)) | cellPoint a w ∈ realMap A.ι '' S}
      = ⋃ i, C i := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hyS, hy⟩
      obtain ⟨k, m, e, φ, v, σ, hσ, he, hφ, hv, hwe, hb, hp⟩ := isNF_nfOf a w
      -- the carrier of `cellPoint a w` is a simplex of `A`
      have hrange : cellPoint a w ∈ Set.range (Rz.{u}.map A.ι) := ⟨y, hy⟩
      rw [mem_range_subcomplex_iff] at hrange
      rw [nf_cellPoint, hp] at hrange
      have hσA : σ ∈ A.obj (op ⦋m⦌) := hrange
      have hbA : K.map e.op a ∈ A.obj (op ⦋k⦌) := by
        rw [hb]; exact A.map φ.op hσA
      haveI : Mono e := SimplexCategory.mono_iff_injective.2 he
      have hk : k ≤ X.len := SimplexCategory.len_le_of_mono e
      have hkey : Rz.{u}.map A.ι
          (cellPoint (X := ⦋k⦌) (⟨K.map e.op a, hbA⟩ : (A : SSet.{u}) _⦋k⦌) v) = cellPoint a w := by
        rw [cellPoint_naturality]
        show cellPoint (K.map e.op a) v = cellPoint a w
        rw [cellPoint_map, hwe]
      have hyv : cellPoint (X := ⦋k⦌) (⟨K.map e.op a, hbA⟩ : (A : SSet.{u}) _⦋k⦌) v ∈ S := by
        have := realization_subcomplex_injective A (hkey.trans hy.symm)
        rw [this]; exact hyS
      refine ⟨⟨⟨k, by omega⟩, e⟩, ?_⟩
      simp only [hC, dif_pos hbA]
      exact ⟨v, hyv, hwe⟩
    · rintro ⟨i, hi⟩
      simp only [hC] at hi
      by_cases hcond : K.map i.2.op a ∈ A.obj (op ⦋(i.1 : ℕ)⦌)
      · rw [dif_pos hcond] at hi
        obtain ⟨v, hv, rfl⟩ := hi
        refine ⟨_, hv, ?_⟩
        show Rz.map A.ι
          (cellPoint (X := ⦋(i.1 : ℕ)⦌)
            (⟨K.map i.2.op a, hcond⟩ : (A : SSet.{u}) _⦋(i.1 : ℕ)⦌) v) = _
        rw [cellPoint_naturality]
        show cellPoint (K.map i.2.op a) v = _
        rw [cellPoint_map]
      · rw [dif_neg hcond] at hi
        exact absurd hi (Set.notMem_empty w)
  rw [hcov]
  refine isClosed_iUnion_of_finite (fun i => ?_)
  simp only [hC]
  by_cases hcond : K.map i.2.op a ∈ A.obj (op ⦋(i.1 : ℕ)⦌)
  · rw [dif_pos hcond]
    have hpre : IsClosed {v : stdSimplex ℝ (Fin ((i.1 : ℕ) + 1)) |
        cellPoint (X := ⦋(i.1 : ℕ)⦌) (⟨K.map i.2.op a, hcond⟩ : (A : SSet.{u}) _⦋(i.1 : ℕ)⦌)
          v ∈ S} :=
      hS.preimage (continuous_cellPoint (K := (A : SSet.{u})) (X := ⦋(i.1 : ℕ)⦌)
        (⟨K.map i.2.op a, hcond⟩ : (A : SSet.{u}) _⦋(i.1 : ℕ)⦌))
    exact (hpre.isCompact.image (stdSimplex.continuous_map _)).isClosed
  · rw [dif_neg hcond]
    exact isClosed_empty

/-! ## Factorization of a compact domain through a skeleton -/

/-- **A continuous map from a compact space into `|K|` factors through a finite skeleton.** -/
theorem exists_skeletal_factorization {Z : Type v} [TopologicalSpace Z] [CompactSpace Z]
    (K : SSet.{u}) (g : C(Z, (SSet.toTop.{u}.obj K : Type u))) :
    ∃ (r : ℕ) (g' : C(Z, RealSpace ((K.skeleton r : K.Subcomplex) : SSet.{u}))),
      ∀ z, realMap (K.skeleton r).ι (g' z) = g z := by
  classical
  obtain ⟨r, hr⟩ := exists_carrierDim_bound K (Set.range g) (isCompact_range g.continuous)
  have hmem : ∀ z, g z ∈ Set.range (realMap (K.skeleton r).ι) := fun z =>
    (mem_range_skeleton_iff K r (g z)).2 (hr _ ⟨z, rfl⟩)
  choose g' hg' using hmem
  have hcont : Continuous g' := by
    rw [continuous_iff_isClosed]
    intro S hS
    have hEq : g' ⁻¹' S = g ⁻¹' (realMap (K.skeleton r).ι '' S) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hz; exact ⟨g' z, hz, hg' z⟩
      · rintro ⟨y, hyS, hy⟩
        have : y = g' z :=
          realization_subcomplex_injective (K.skeleton r) (hy.trans (hg' z).symm)
        rwa [← this]
    rw [hEq]
    exact (isClosedMap_realization_subcomplex (K.skeleton r) S hS).preimage g.continuous
  exact ⟨r, ⟨g', hcont⟩, hg'⟩

end NerveTopology
