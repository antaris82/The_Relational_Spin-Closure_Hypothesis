import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Contractible
import RequestProject.Spine.Nerve.Geometry.RealizedBoundary

/-!
# Task 17, WP2/WP3/WP5 — the topology of the realized standard cell

Task 16 identified the *points* of the geometric realization `SSet.toTop` of the standard
simplex and of its subcomplexes, and the *image* of `|∂Δ[r]| → |Δ[r]|` as a set of barycentric
coordinate tuples.  This module upgrades those set-theoretic statements to statements about
topological spaces, using only the realization functor of the pinned library (no second
model is introduced) and the Task-16 coordinates `SpineTask16.coord`.

## Contents

* `SpineTask17.simplexHomeo` (WP3) — the **homeomorphism** `|Δ[n]| ≃ₜ stdSimplex ℝ (Fin (n+1))`,
  built from the library identification `SSet.toTopSimplex`.  Its underlying function is
  *definitionally* the Task-16 coordinate bijection (`coe_simplexHomeo`), so all Task-16
  coordinate statements apply verbatim.  Vertices go to barycentric vertices
  (`simplexHomeo_vertex`) and the simplicial operators act by `stdSimplex.map`
  (`simplexHomeo_naturality`).
* `SpineTask17.compactSpace_realized_subcomplex` — for **every** subcomplex `A ≤ Δ[r]` the
  realization `|A|` is compact.  The proof is a finite cover of `|A|` by the realizations of
  the top-dimensional simplices of `A` (`subCover_surjective`), which uses the Task-16 normal
  form and the splitting of epimorphisms in the simplex category.
* `SpineTask17.isClosedEmbedding_subCoord` (WP2, general form) — for every subcomplex
  `A ≤ Δ[r]`, the realized inclusion `|A| → |Δ[r]|` is a **closed topological embedding**;
  equivalently `|A|` carries the subspace topology of the barycentric model.
* `SpineTask17.boundaryHomeo` (WP2, the boxed target) — the **homeomorphism**
  `|∂Δ[r]| ≃ₜ {x ∈ Σ_r : ∃ i, x i = 0}` onto the barycentric boundary locus, compatible with
  the Task-16 coordinates (`coe_boundaryHomeo`).
* `SpineTask17.contractibleSpace_realized_simplex` (WP5) — `|Δ[r]|` is contractible (it is
  homeomorphic to a nonempty convex set).
* low-dimensional cases: `|∂Δ[0]|` is empty, `|∂Δ[1]|` is a discrete two-point space
  (`boundaryOneHomeo`), i.e. the `0`-sphere.

Nothing here is assumed: `SSet.toTop` is used as given, and compactness and Hausdorffness are
*proved*, never postulated, before the compact-to-Hausdorff embedding criterion is invoked.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Topology SimplexCategory

universe u

namespace SpineTask17

/-! ## WP3 : the realized standard simplex *is* the geometric standard simplex -/

/-- **WP3.**  The realization of the standard `n`-simplex is homeomorphic to the geometric
standard simplex `stdSimplex ℝ (Fin (n+1))`.  This is the pinned library identification
`SSet.toTopSimplex`, read as a homeomorphism. -/
def simplexHomeo (n : SimplexCategory) :
    ↥(SSet.toTop.{u}.obj (SSet.stdSimplex.obj n)) ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (SSet.toTopSimplex.{u}.app n)).trans Homeomorph.ulift

/-- The homeomorphism of `simplexHomeo` *is* the Task-16 coordinate bijection: the two models
are literally the same map, so no second coordinate system is introduced. -/
theorem coe_simplexHomeo (n : SimplexCategory) :
    ⇑(simplexHomeo.{u} n) = SpineTask16.coord.{u} n := rfl

/-- Naturality of `simplexHomeo` in the simplex category (Task-16 `coord_naturality`). -/
theorem simplexHomeo_naturality {n m : SimplexCategory} (a : n ⟶ m)
    (t : SpineTask16.Rz.{u}.obj (SSet.stdSimplex.obj n)) :
    simplexHomeo m (SpineTask16.Rz.map (SSet.stdSimplex.map a) t)
      = stdSimplex.map a.toOrderHom (simplexHomeo n t) :=
  SpineTask16.coord_naturality a t

instance compactSpace_realized_simplex (n : ℕ) :
    CompactSpace ↥(SSet.toTop.{u}.obj (Δ[n] : SSet.{u})) :=
  (simplexHomeo.{u} ⦋n⦌).symm.compactSpace

instance t2Space_realized_simplex (n : ℕ) :
    T2Space ↥(SSet.toTop.{u}.obj (Δ[n] : SSet.{u})) :=
  (simplexHomeo.{u} ⦋n⦌).symm.t2Space

/-- **WP5.**  The realized standard simplex is contractible: it is homeomorphic to a nonempty
convex subset of `Fin (n+1) → ℝ`. -/
instance contractibleSpace_realized_simplex (n : ℕ) :
    ContractibleSpace ↥(SSet.toTop.{u}.obj (Δ[n] : SSet.{u})) := by
  have : ContractibleSpace (stdSimplex ℝ (Fin ((⦋n⦌ : SimplexCategory).len + 1))) := by
    simp only [len_mk]
    exact (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨_, (stdSimplex.vertex (0 : Fin (n + 1))).2⟩
  exact (simplexHomeo.{u} ⦋n⦌).contractibleSpace

/-- The `i`-th vertex of the realized standard `n`-simplex: the realization of the vertex
`Δ[0] ⟶ Δ[n]`, evaluated at the unique point of `|Δ[0]|`. -/
def realizedVertex {n : ℕ} (i : Fin (n + 1)) : SpineTask16.Rz.{u}.obj (Δ[n] : SSet.{u}) :=
  SpineTask16.Rz.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))
    ((SpineTask16.coord ⦋0⦌).symm (stdSimplex.vertex (0 : Fin 1)))

/-- **WP3(3).**  Vertices go to the standard barycentric vertices. -/
theorem simplexHomeo_vertex {n : ℕ} (i : Fin (n + 1)) :
    simplexHomeo.{u} ⦋n⦌ (realizedVertex i) = stdSimplex.vertex i := by
  rw [coe_simplexHomeo, realizedVertex, SpineTask16.coord_naturality, Equiv.apply_symm_apply,
    stdSimplex.map_vertex]
  rfl

/-! ## WP2 : compactness of the realization of a subcomplex of `Δ[r]` -/

variable {r : ℕ}

/-- A canonical epimorphism `⦋r⦌ ⟶ ⦋k⦌` (it is surjective as soon as `k ≤ r`). -/
def collapse (k r : ℕ) : (⦋r⦌ : SimplexCategory) ⟶ ⦋k⦌ :=
  SimplexCategory.Hom.mk ⟨fun x => ⟨min x.val k, lt_of_le_of_lt (min_le_right _ _) (by simp)⟩,
    fun a b hab => by
      simp only [Fin.mk_le_mk]
      exact min_le_min (by exact_mod_cast hab) le_rfl⟩

lemma collapse_surjective (k r : ℕ) (h : k ≤ r) :
    Function.Surjective (collapse k r).toOrderHom := by
  intro a
  have ha : (a : ℕ) < r + 1 := by have := a.isLt; simp only [len_mk] at this; omega
  refine ⟨⟨a.val, by simpa using ha⟩, ?_⟩
  apply Fin.ext
  have hak : (a : ℕ) ≤ k := by have := a.isLt; simp only [len_mk] at this; omega
  simp [collapse, SimplexCategory.Hom.toOrderHom_mk, hak]

/-- A strictly monotone `⦋k⦌ ⟶ ⦋r⦌` forces `k ≤ r`. -/
lemma le_of_strictMono {k : ℕ} (e : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌)
    (h : StrictMono e.toOrderHom) : k ≤ r := by
  have := Fintype.card_le_of_injective _ h.injective
  simp only [Fintype.card_fin, len_mk] at this
  omega

/-- The finite index set of the `r`-dimensional simplices of a subcomplex `A ≤ Δ[r]`. -/
abbrev topIdx (A : (Δ[r] : SSet.{u}).Subcomplex) : Type :=
  {g : (⦋r⦌ : SimplexCategory) ⟶ ⦋r⦌ // SpineTask16.faceSimplex.{u} g ∈ A.obj (op ⦋r⦌)}

instance (A : (Δ[r] : SSet.{u}).Subcomplex) : Finite (topIdx.{u} A) := Subtype.finite

/-- The finite cover of `|A|` by realized `r`-simplices of `A`. -/
def subCover (A : (Δ[r] : SSet.{u}).Subcomplex)
    (p : Σ _g : topIdx.{u} A, ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    ↥(SSet.toTop.{u}.obj (A : SSet.{u})) :=
  SpineTask16.Rz.map (SpineTask16.subFaceMap A p.1.1 p.1.2) p.2

/-- The cover is surjective: every point of `|A|` lies on a realized `r`-simplex of `A`.
This uses the Task-16 normal form (a point is an interior point of a realized *face*) and the
splitting of the collapse epimorphism. -/
theorem subCover_surjective (A : (Δ[r] : SSet.{u}).Subcomplex) :
    Function.Surjective (subCover.{u} A) := by
  intro x
  obtain ⟨k, e, hmem, v, hmono, -, rfl⟩ := SpineTask16.subNormalForm A x
  have hkr : k ≤ r := le_of_strictMono e hmono
  set α : (⦋r⦌ : SimplexCategory) ⟶ ⦋k⦌ := collapse k r with hα
  have hepi : Epi α := SimplexCategory.epi_iff_surjective.2 (collapse_surjective k r hkr)
  have hsplit : IsSplitEpi α := isSplitEpi_of_epi α
  set s := CategoryTheory.section_ α with hs
  have hsα : s ≫ α = 𝟙 _ := IsSplitEpi.id α
  set g : (⦋r⦌ : SimplexCategory) ⟶ ⦋r⦌ := α ≫ e with hg
  have hgmem : SpineTask16.faceSimplex.{u} g ∈ A.obj (op ⦋r⦌) := A.map α.op hmem
  have hmaps : SSet.stdSimplex.map s ≫ SpineTask16.subFaceMap A g hgmem
      = SpineTask16.subFaceMap A e hmem := by
    rw [← cancel_mono A.ι, Category.assoc, SpineTask16.subFaceMap_comp_ι,
      SpineTask16.subFaceMap_comp_ι, ← Functor.map_comp, hg, ← Category.assoc, hsα,
      Category.id_comp]
  refine ⟨⟨⟨g, hgmem⟩, SpineTask16.Rz.map (SSet.stdSimplex.map s)
    ((SpineTask16.coord ⦋k⦌).symm v)⟩, ?_⟩
  show SpineTask16.Rz.map (SpineTask16.subFaceMap A g hgmem) _ = _
  rw [← types_comp_apply (SpineTask16.Rz.map (SSet.stdSimplex.map s))
      (SpineTask16.Rz.map (SpineTask16.subFaceMap A g hgmem)),
    ← Functor.map_comp, hmaps]

lemma continuous_subCover (A : (Δ[r] : SSet.{u}).Subcomplex) :
    Continuous (subCover.{u} A) :=
  continuous_sigma fun g => (SSet.toTop.map (SpineTask16.subFaceMap A g.1 g.2)).hom.continuous

/-- **The realization of a subcomplex of a standard simplex is compact.** -/
instance compactSpace_realized_subcomplex (A : (Δ[r] : SSet.{u}).Subcomplex) :
    CompactSpace ↥(SSet.toTop.{u}.obj (A : SSet.{u})) := by
  refine ⟨?_⟩
  rw [← (subCover_surjective A).range_eq, ← Set.image_univ]
  exact isCompact_univ.image (continuous_subCover A)

/-! ## WP2 : the realized inclusion of a subcomplex is a closed embedding -/

lemma continuous_subCoord (A : (Δ[r] : SSet.{u}).Subcomplex) :
    Continuous (show ↥(SSet.toTop.{u}.obj (A : SSet.{u})) → stdSimplex ℝ (Fin (r + 1)) from
      SpineTask16.subCoord.{u} A) :=
  (simplexHomeo.{u} ⦋r⦌).continuous.comp (SSet.toTop.map A.ι).hom.continuous

lemma injective_subCoord (A : (Δ[r] : SSet.{u}).Subcomplex) :
    Function.Injective (SpineTask16.subCoord.{u} A) :=
  (SpineTask16.coord ⦋r⦌).injective.comp (SpineTask16.subcomplexMono A)

/-- **WP2, general form.**  For every subcomplex `A ≤ Δ[r]`, the barycentric coordinate map of
`|A|` is a closed topological embedding into the geometric standard simplex.  In particular
`|A|` carries the subspace topology. -/
theorem isClosedEmbedding_subCoord (A : (Δ[r] : SSet.{u}).Subcomplex) :
    IsClosedEmbedding (show ↥(SSet.toTop.{u}.obj (A : SSet.{u})) → stdSimplex ℝ (Fin (r + 1))
      from SpineTask16.subCoord.{u} A) :=
  (continuous_subCoord A).isClosedEmbedding (injective_subCoord A)

/-- The realization of the inclusion of a subcomplex `A ≤ Δ[r]` into `|Δ[r]|` is itself a
closed topological embedding. -/
theorem isClosedEmbedding_realization_subcomplex (A : (Δ[r] : SSet.{u}).Subcomplex) :
    IsClosedEmbedding (show ↥(SSet.toTop.{u}.obj (A : SSet.{u})) →
      ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})) from SpineTask16.Rz.map A.ι) :=
  ((SSet.toTop.map A.ι).hom.continuous).isClosedEmbedding (SpineTask16.subcomplexMono A)

/-! ## WP2, the boxed target : the realized boundary is the barycentric boundary locus -/

/-- The barycentric boundary locus of the geometric standard `r`-simplex. -/
def bdLocus (r : ℕ) : Set (stdSimplex ℝ (Fin (r + 1))) := {x | ∃ i, x i = 0}

/-- The realized boundary inclusion is a closed embedding into the geometric simplex. -/
theorem isClosedEmbedding_bdCoord (r : ℕ) :
    IsClosedEmbedding (show ↥(SSet.toTop.{u}.obj
      (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})) → stdSimplex ℝ (Fin (r + 1))
      from SpineTask16.bdCoord.{u} r) :=
  isClosedEmbedding_subCoord (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)

/-- **WP2 (the boxed target).**  `|∂Δ[r]|` is *homeomorphic*, not merely in bijection, with the
barycentric boundary locus `{x : ∃ i, x i = 0}` of the geometric standard `r`-simplex, by the
Task-16 coordinate map. -/
def boundaryHomeo (r : ℕ) :
    ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})) ≃ₜ bdLocus r :=
  (isClosedEmbedding_bdCoord.{u} r).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (SpineTask16.range_bdCoord.{u} r))

@[simp] theorem coe_boundaryHomeo (r : ℕ)
    (x : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    ((boundaryHomeo.{u} r x : bdLocus r) : stdSimplex ℝ (Fin (r + 1)))
      = SpineTask16.bdCoord.{u} r x := rfl

/-- The realized boundary inclusion `|∂Δ[r]| → |Δ[r]|` is a closed embedding. -/
theorem isClosedEmbedding_realization_boundary (r : ℕ) :
    IsClosedEmbedding (show ↥(SSet.toTop.{u}.obj
      (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})) →
      ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})) from
      SpineTask16.Rz.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) :=
  isClosedEmbedding_realization_subcomplex (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)

/-- The realized boundary is a closed subset of `|Δ[r]|`; equivalently its complement, the
relative interior, is open. -/
theorem isOpen_compl_realized_boundary (r : ℕ) :
    IsOpen (X := ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))
      (Set.range (SpineTask16.Rz.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι))ᶜ :=
  (isClosedEmbedding_realization_boundary.{u} r).isClosed_range.isOpen_compl

/-! ## Low-dimensional cases -/

/-- `r = 0` : the realized boundary is empty. -/
theorem boundaryZero_isEmpty :
    IsEmpty ↥(SSet.toTop.{u}.obj (((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex)) : SSet.{u})) :=
  SpineTask16.boundaryZero_realization_isEmpty

lemma vertex_mem_bdLocus_one (i : Fin 2) : stdSimplex.vertex i ∈ bdLocus 1 := by
  refine ⟨i + 1, ?_⟩
  have h : i + 1 ≠ i := by fin_cases i <;> decide
  simp [stdSimplex.vertex, h]

/-- `r = 1` : the barycentric boundary locus of the geometric `1`-simplex is exactly its two
vertices. -/
def twoPointEquiv : Fin 2 ≃ bdLocus 1 where
  toFun i := ⟨stdSimplex.vertex i, vertex_mem_bdLocus_one i⟩
  invFun v := if ((v : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 0 = 0 then 1 else 0
  left_inv i := by fin_cases i <;> simp [stdSimplex.vertex]
  right_inv v := by
    obtain ⟨j, hj⟩ := v.2
    by_cases h0 : ((v : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 0 = 0
    · have hv : (v : stdSimplex ℝ (Fin 2)) = stdSimplex.vertex 1 := by
        have hs := stdSimplex.sum_eq_one (v : stdSimplex ℝ (Fin 2))
        rw [Fin.sum_univ_two, h0, zero_add] at hs
        ext k; fin_cases k <;> simp [stdSimplex.vertex, h0, hs]
      simp only [h0, if_pos]
      exact Subtype.ext hv.symm
    · have h1 : ((v : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 = 0 := by
        fin_cases j
        · exact absurd hj h0
        · exact hj
      have hv : (v : stdSimplex ℝ (Fin 2)) = stdSimplex.vertex 0 := by
        have hs := stdSimplex.sum_eq_one (v : stdSimplex ℝ (Fin 2))
        rw [Fin.sum_univ_two, h1, add_zero] at hs
        ext k; fin_cases k <;> simp [stdSimplex.vertex, h1, hs]
      simp only [h0, if_false]
      exact Subtype.ext hv.symm

instance : Finite (bdLocus 1) := Finite.of_equiv _ twoPointEquiv

/-- The barycentric boundary locus of the geometric `1`-simplex is a discrete two-point space,
i.e. the `0`-sphere. -/
def bdLocusOneHomeo : bdLocus 1 ≃ₜ Fin 2 where
  toEquiv := twoPointEquiv.symm
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- **WP6, `r = 1`.**  `|∂Δ[1]|` is homeomorphic to the discrete two-point space `Fin 2`, that
is, to `S⁰`.  (`Fin 2` carries the discrete topology.) -/
def boundaryOneHomeo :
    ↥(SSet.toTop.{u}.obj (((∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u})) ≃ₜ Fin 2 :=
  (boundaryHomeo.{u} 1).trans bdLocusOneHomeo

end SpineTask17
