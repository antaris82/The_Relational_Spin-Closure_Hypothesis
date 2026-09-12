import RequestProject.Spine.AlgebraicTopology.SimplicialSkeleton
import RequestProject.Spine.Nerve.Basic.UnitChainMap

/-!
# Task 13, WP1/WP12 : the normalization applied to the **frozen canonical data**

Task 13 must not replace the canonical comparison map.  The fixed objects of WP1 are

* `K = NerveGeom.coverNerveSSet 𝓤`, the cover nerve as a simplicial set,
* `|K| = NerveGeom.coverNerveRealization 𝓤 = SSet.toTop.obj K`,
* `η_K : K ⟶ TopCat.toSSet.obj |K|`, the unit of `SSet.toTop ⊣ TopCat.toSSet`,
* `J = C_*(η_K) = NerveGeom.chainMap 𝓤` (Task 10, `chainMap_eq_unitChainMap`).

This module records, at theorem level, that the Objective-A normalization applies to exactly
these objects, and that `J` descends to the normalized complexes.

## Contents

* `nerveChain_eq`, `nerveBoundary_eq` — the Task-9 chain module and boundary of the nerve are
  the general `SSetChain`/`sSetBoundary` of `K`, definitionally, so `degenSubmodule`,
  `NormChain`, `normProj`, `normInc` and the homotopy of Objective A are statements about the
  *actual* project complex;
* `normJ` — the normalized comparison map, obtained by applying the natural construction
  `normMap` to the **unit** `η_K`; it is not a new choice;
* `normJ_normProj` — the commuting square `p ∘ J = normJ ∘ p`, i.e. `J` descends;
* `normJ_comm` — `normJ` is a chain map for the normalized differentials.

Nothing here assumes anything about singular relative homology; see
`TASK13_NORMALIZED_SKELETAL_COMPARISON.md` for the audit of what is still missing.
-/

noncomputable section

namespace SpineTask13

open CategoryTheory Opposite Simplicial AlgebraicTopology NerveGeom

universe w u

variable {X : Type w} {ι : Type u}

/-- The Task-9 simplicial chain module of the nerve **is** the general chain module of the
simplicial set `K = N(𝓤)`. -/
theorem nerveChain_eq (U : ι → Set X) (q : ℕ) :
    SimpChain U q = SSetChain (coverNerveSSet U) q := rfl

/-- The Task-9 unnormalized boundary **is** the general boundary of `K = N(𝓤)`. -/
theorem nerveBoundary_eq (U : ι → Set X) (q : ℕ) :
    simpBoundary U q = sSetBoundary (coverNerveSSet U) q := rfl

/-- The Task-9 singular chain module of `|K|` **is** the general chain module of the singular
simplicial set of `|K|`. -/
theorem singChain_eq (U : ι → Set X) (q : ℕ) :
    SingChain (coverNerveRealization U) q
      = SSetChain (TopCat.toSSet.obj (coverNerveRealization U)) q := rfl

/-- **WP12.  The normalized comparison map**, obtained from the canonical unit `η_K` by the
natural construction of Objective A.  No new map is chosen. -/
def normJ (U : ι → Set X) (q : ℕ) :
    NormChain (coverNerveSSet U) q →ₗ[ZMod 2]
      NormChain (TopCat.toSSet.obj (coverNerveRealization U)) q :=
  normMap (sSetTopAdj.unit.app (coverNerveSSet U)) q

/-- **WP12.  `J` descends to the normalized complexes**: `p ∘ J = normJ ∘ p`, with `J` the
*actual* Task-9 chain map `NerveGeom.chainMap`. -/
theorem normJ_normProj (U : ι → Set X) (q : ℕ) :
    (normProj (TopCat.toSSet.obj (coverNerveRealization U)) q).comp (chainMap U q)
      = (normJ U q).comp (normProj (coverNerveSSet U) q) := by
  rw [chainMap_eq_unitChainMap]
  exact normProj_natural (sSetTopAdj.unit.app (coverNerveSSet U)) q

/-- `normJ` is a chain map for the normalized differentials. -/
theorem normJ_comm (U : ι → Set X) (q : ℕ) :
    (normJ U q).comp (normBoundary (coverNerveSSet U) q)
      = (normBoundary (TopCat.toSSet.obj (coverNerveRealization U)) q).comp (normJ U (q + 1)) :=
  normMap_comm (sSetTopAdj.unit.app (coverNerveSSet U)) q

/-- `J` carries degenerate simplicial chains to degenerate singular chains: the canonical
comparison respects the degeneracy filtration. -/
theorem chainMap_degen_mem (U : ι → Set X) (q : ℕ) {x : SimpChain U q}
    (hx : x ∈ degenSubmodule (coverNerveSSet U) q) :
    chainMap U q x ∈ degenSubmodule (TopCat.toSSet.obj (coverNerveRealization U)) q := by
  rw [chainMap_eq_unitChainMap]
  exact sSetChainMap_degen_mem (sSetTopAdj.unit.app (coverNerveSSet U)) q hx

/-! ## The normalization of the frozen data, spelled out

These are the Objective-A theorems specialised to `K = N(𝓤)`; they are restatements, not new
results, and exist so that the WP1 freeze is visibly respected. -/

theorem nerve_normProj_comp_normInc (U : ι → Set X) (q : ℕ) :
    (normProj (coverNerveSSet U) q).comp (normInc (coverNerveSSet U) q) = LinearMap.id :=
  normProj_comp_normInc (coverNerveSSet U) q

theorem nerve_normHtpy_zero (U : ι → Set X) :
    (sSetBoundary (coverNerveSSet U) 0).comp (normHtpy (coverNerveSSet U) 0)
      = LinearMap.id + proj (coverNerveSSet U) 0 :=
  normHtpy_zero (coverNerveSSet U)

theorem nerve_normHtpy_succ (U : ι → Set X) (q : ℕ) :
    (sSetBoundary (coverNerveSSet U) (q + 1)).comp (normHtpy (coverNerveSSet U) (q + 1))
        + (normHtpy (coverNerveSSet U) q).comp (sSetBoundary (coverNerveSSet U) q)
      = LinearMap.id + proj (coverNerveSSet U) (q + 1) :=
  normHtpy_succ (coverNerveSSet U) q

/-- The normalized chains of the nerve are free on the nondegenerate nerve simplices. -/
def nerveNormChainEquiv (U : ι → Set X) (q : ℕ) :
    NormChain (coverNerveSSet U) q ≃ₗ[ZMod 2]
      (↥((coverNerveSSet U).nonDegenerate q) →₀ ZMod 2) :=
  normChainEquiv (coverNerveSSet U) q

end SpineTask13
