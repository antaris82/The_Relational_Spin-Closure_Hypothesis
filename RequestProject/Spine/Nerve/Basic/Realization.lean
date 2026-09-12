import RequestProject.Spine.Cohomology.Cohomology
import RequestProject.Spine.Nerve.Basic.Cover

/-!
# Task 9, WP4–WP5 : the geometric realization `|N(𝓤)|` and its characteristic simplices

## WP4 — audit of the realization infrastructure in the pinned library

| item | status |
| --- | --- |
| geometric realization of a simplicial set, `SSet.toTop : SSet ⥤ TopCat` | `MATHLIB_NATIVE` |
| realization as a left Kan extension of `SimplexCategory.toTop` | `MATHLIB_NATIVE` |
| the singular simplicial set `TopCat.toSSet` | `MATHLIB_NATIVE` |
| the adjunction `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` | `MATHLIB_NATIVE` |
| `SSet.toTopSimplex : stdSimplex ⋙ toTop ≅ SimplexCategory.toTop` (realization of the standard simplices) | `MATHLIB_NATIVE` |
| topology on the realization (colimit/quotient topology, inherited from the Kan extension) | `MATHLIB_NATIVE` |
| canonical map `Δⁿ_top → |S|` attached to an `n`-simplex | `MATHLIB_PARTIAL` — supplied by the unit of `sSetTopAdj`, but not packaged; done here |
| face/degeneracy compatibility of those maps | `MATHLIB_PARTIAL` — it is the naturality of the unit; recorded here as theorems |
| CW/simplicial-complex realization as an alternative | `MISSING` for our purpose (no comparison theorem attached) |
| simplicial-to-singular (co)homology comparison theorem | `MISSING` (see `RequestProject.Spine.Nerve.Cochain.ComparisonSpec`) |

Because Mathlib already supplies the correct geometric realization of a simplicial set, it is
**reused**: `|N(𝓤)|` below is literally `SSet.toTop.obj (coverNerveSSet 𝓤)`.  No auxiliary
topological space is introduced and nothing is *declared* to be a realization.

## WP5 — the canonical singular simplex of a simplicial simplex

For a simplicial set `S`, the unit

`η_S : S ⟶ TopCat.toSSet.obj (SSet.toTop.obj S)`

of the adjunction is a **morphism of simplicial sets**.  Evaluated in degree `n` it sends a
simplicial `n`-simplex `σ ∈ Sₙ` to a singular `n`-simplex of `|S|`, i.e. to a continuous map
`Δⁿ_top → |S|`.  This is *the* characteristic map of `σ`: by the universal property
(`charSimplex_universal`) it is the unique family compatible with maps out of `|S|`, so no
choice is made anywhere.

Because `η_S` is a map of simplicial sets, compatibility with **faces** and with
**degeneracies** is automatic and is recorded here as `charSimplex_face` and
`charSimplex_degen` — both are instances of the single naturality statement
`charSimplex_reindex`.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

variable {X : Type w} {ι : Type u}

/-! ## The geometric realization of the cover nerve -/

/-- **`|N(𝓤)|`, the geometric realization of the canonical simplicial cover nerve.**  It is
Mathlib's geometric realization functor applied to the simplicial set of WP2 — not an
auxiliary space declared to be a realization. -/
def coverNerveRealization (U : ι → Set X) : TopCat.{u} :=
  SSet.toTop.obj (coverNerveSSet U)

theorem coverNerveRealization_def (U : ι → Set X) :
    coverNerveRealization U = SSet.toTop.obj (coverNerveSSet U) := rfl

/-! ## The characteristic singular simplex of a nerve simplex -/

/-- **The canonical singular `n`-simplex `|σ|` of a simplicial `n`-simplex `σ` of the nerve**:
the value at `σ` of the unit of the adjunction `SSet.toTop ⊣ TopCat.toSSet`.  Concretely it is
a continuous map `Δⁿ_top → |N(𝓤)|` (see `charMap`). -/
def charSimplex (U : ι → Set X) (n : ℕ) (σ : Nerve U n) :
    Mod2Cohomology.Simplex (coverNerveRealization U) n :=
  (sSetTopAdj.unit.app (coverNerveSSet U)).app (op (SimplexCategory.mk n)) σ

/-- The characteristic simplex, read as an honest continuous map from the standard topological
`n`-simplex into the realization. -/
def charMap (U : ι → Set X) (n : ℕ) (σ : Nerve U n) :
    C(stdSimplex ℝ (Fin (n + 1)), coverNerveRealization U) :=
  (coverNerveRealization U).toSSetObjEquiv (op (SimplexCategory.mk n)) (charSimplex U n σ)

/-- **Naturality of the characteristic simplex**: reindexing a nerve simplex along any
morphism of the simplex category reindexes its characteristic singular simplex along the same
morphism.  This is the statement that `σ ↦ |σ|` is a map of simplicial sets. -/
theorem charSimplex_reindex (U : ι → Set X) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (σ : Nerve U n) :
    charSimplex U m ((coverNerveSSet U).map f.op σ)
      = Mod2Cohomology.reindex f (charSimplex U n σ) :=
  congrFun ((sSetTopAdj.unit.app (coverNerveSSet U)).naturality f.op) σ

/-- **WP5, face compatibility.**  `|∂ᵢσ| = |σ| ∘ δᵢ`: the characteristic simplex of the `i`-th
face of `σ` is the `i`-th face of the characteristic simplex of `σ`. -/
theorem charSimplex_face (U : ι → Set X) {n : ℕ} (i : Fin (n + 2)) (σ : Nerve U (n + 1)) :
    charSimplex U n (CechZ2.face i σ)
      = Mod2Cohomology.face i (charSimplex U (n + 1) σ) :=
  charSimplex_reindex U (SimplexCategory.δ i) σ

/-- **WP5, degeneracy compatibility.**  `|sᵢσ|` is the degenerate singular simplex obtained
from `|σ|` by reindexing along the standard codegeneracy `σᵢ`. -/
theorem charSimplex_degen (U : ι → Set X) {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    charSimplex U (n + 1) (degen i σ)
      = Mod2Cohomology.reindex (SimplexCategory.σ i) (charSimplex U n σ) :=
  charSimplex_reindex U (SimplexCategory.σ i) σ

/-! ## The characteristic simplices are not a choice -/

/-- **WP5, universality.**  The family `σ ↦ |σ|` is the unit of the geometric-realization
adjunction, hence it is *universal*: every map of simplicial sets from the nerve into the
singular simplicial set of a space `Y` factors uniquely through it along a continuous map
`|N(𝓤)| → Y`.  In particular no other family of singular simplices can be substituted for it,
and it is not an arbitrary choice of continuous maps out of the standard simplices. -/
theorem charSimplex_universal (U : ι → Set X) (Y : TopCat.{u})
    (φ : coverNerveSSet U ⟶ TopCat.toSSet.obj Y) :
    ∃! g : coverNerveRealization U ⟶ Y,
      sSetTopAdj.unit.app (coverNerveSSet U) ≫ TopCat.toSSet.map g = φ := by
  have key : ∀ g : coverNerveRealization U ⟶ Y,
      sSetTopAdj.unit.app (coverNerveSSet U) ≫ TopCat.toSSet.map g
        = sSetTopAdj.homEquiv (coverNerveSSet U) Y g :=
    fun g => (Adjunction.homEquiv_unit sSetTopAdj (coverNerveSSet U) Y g).symm
  refine ⟨(sSetTopAdj.homEquiv _ _).symm φ, ?_, ?_⟩
  · show sSetTopAdj.unit.app (coverNerveSSet U)
        ≫ TopCat.toSSet.map ((sSetTopAdj.homEquiv (coverNerveSSet U) Y).symm φ) = φ
    rw [key]
    exact (sSetTopAdj.homEquiv _ _).apply_symm_apply φ
  · intro g hg
    rw [key] at hg
    rw [← hg, (sSetTopAdj.homEquiv _ _).symm_apply_apply]

end NerveGeom
