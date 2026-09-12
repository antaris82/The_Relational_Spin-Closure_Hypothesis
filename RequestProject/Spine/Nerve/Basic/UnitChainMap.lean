import RequestProject.Spine.AlgebraicTopology.SimplicialChains
import RequestProject.Spine.Nerve.Basic.ChainMap

/-!
# The nerve chain map **is** the linearisation of the adjunction unit

The Task-9 layer built, by hand,

* `NerveGeom.simpBoundary` — the unsigned boundary on `Cₙ^simp(N(𝓤);ℤ₂)`,
* `NerveGeom.singBoundary` — the unsigned boundary on `Cₙ^sing(|N(𝓤)|;ℤ₂)`,
* `NerveGeom.chainMap`    — the linear extension of the characteristic simplex `σ ↦ |σ|`.

This module proves at theorem level that all three are values of *one* construction, the free
`ℤ₂`-linearisation of a simplicial set.  That construction is generic and lives in
`RequestProject.Spine.AlgebraicTopology.SimplicialChains`
(`NerveGeom.SSetChain`, `NerveGeom.sSetBoundary`, `NerveGeom.sSetChainMap`,
`NerveGeom.sSetBoundary_naturality`); only the *identifications* with the nerve data are
Nerve-specific and therefore stated here:

* `simpBoundary_eq`, `singBoundary_eq` — the two Task-9 boundaries are the linearised
  boundaries of `N(𝓤)` and of `Sing|N(𝓤)|` respectively;
* `chainMap_eq_unitChainMap` — **the Task-9 chain map `J` is exactly `C_*(η_K)`**, the
  linearisation of the unit `η_K : K ⟶ Sing|K|` of `SSet.toTop ⊣ TopCat.toSSet`, for
  `K = N(𝓤)`.

Consequently `chainMap_comm` of Task 9 is a special case of `sSetBoundary_naturality`
(`chainMap_comm_of_unit`), so no second, unrelated chain map exists in the project: the
carriers are literally the same types and the maps are literally the same functions.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

/-! ## The Task-9 data are values of the generic linearisation -/

variable {X : Type w} {ι : Type u}

/-- The Task-9 simplicial boundary is the linearised boundary of the simplicial nerve. -/
theorem simpBoundary_eq (U : ι → Set X) (n : ℕ) :
    simpBoundary U n = sSetBoundary (coverNerveSSet U) n := rfl

/-- The Task-9 singular boundary is the linearised boundary of the singular simplicial set. -/
theorem singBoundary_eq (R : TopCat.{u}) (n : ℕ) :
    singBoundary R n = sSetBoundary (TopCat.toSSet.obj R) n := rfl

/-- **`J = C_*(η_K)`.**

The Task-9 chain map `J : C_*^simp(N(𝓤);ℤ₂) → C_*^sing(|N(𝓤)|;ℤ₂)` is *literally* the free
`ℤ₂`-linearisation of the unit `η_K : K ⟶ TopCat.toSSet.obj (SSet.toTop.obj K)` of the
realisation/singular adjunction, for `K = N(𝓤)`.  The two carriers are the same type, not
merely canonically isomorphic ones, so the identification is an equality of linear maps. -/
theorem chainMap_eq_unitChainMap (U : ι → Set X) (n : ℕ) :
    chainMap U n = sSetChainMap (sSetTopAdj.unit.app (coverNerveSSet U)) n := rfl

/-- The Task-9 commutation theorem `∂_sing ∘ J = J ∘ ∂_simp` is the naturality of the unit,
after linearisation. -/
theorem chainMap_comm_of_unit (U : ι → Set X) (n : ℕ) :
    (singBoundary (coverNerveRealization U) n).comp (chainMap U (n + 1))
      = (chainMap U n).comp (simpBoundary U n) :=
  (sSetBoundary_naturality (sSetTopAdj.unit.app (coverNerveSSet U)) n).symm

end NerveGeom
