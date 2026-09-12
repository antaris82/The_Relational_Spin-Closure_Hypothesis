import RequestProject.Spine.Nerve.Basic.UnitChainMap
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Task 11, WP14 : production-pin compile probes for the upstream delta audit

This module contains **only** compile probes for the Task-11 upstream audit
(`TASK11_UPSTREAM_DELTA_AUDIT.md`).  Nothing here proves any part of the geometric
comparison, and nothing in the production Spine depends on this file.

It records, *inside the pinned environment*, three facts that the audit needs.

1. `SpineTask11.unitChainComplexMap` — the pinned Mathlib library already lets one form the
   canonical comparison morphism of chain complexes
   `C_*(K;R) ⟶ C_*^sing(|K|;R)` in the *generic* form
   `((SSet.singularChainComplexFunctor C).obj R).map (sSetTopAdj.unit.app K)`,
   because the pin contains `AlgebraicTopology.SSet.singularChainComplexFunctor`,
   `AlgebraicTopology.singularChainComplexFunctor`, `SSet.toTop`, `TopCat.toSSet` and
   `sSetTopAdj`.  The target of that morphism is, by `rfl`, the generic simplicial
   chain complex of `Sing |K|` (`unitChainComplexMap_target`).
2. `SpineTask11.unitChainComplexMap_naturality` — that morphism is natural in `K`; this is
   the naturality of the adjunction unit, and it is *all* that the pinned library gives.
3. `SpineTask11.UnitQuasiIsoStatement` — the statement that this morphism is a
   quasi-isomorphism, i.e. exactly the theorem the audit searched current upstream Mathlib
   for.  **It is a `Prop`, deliberately left unproved**: neither the pin nor the audited
   upstream commit contains a proof (see `TASK11_UPSTREAM_DELTA_AUDIT.md`, WP5 and WP16).
   No declaration consumes it.

`SpineTask11.taskNine_and_mathlib_share_the_unit` records that the Task-9/Task-10 chain map
and the generic Mathlib morphism above are obtained by applying two linearisation
constructions to **the same** morphism of simplicial sets, namely `sSetTopAdj.unit.app K`
for `K = N(𝓤)`.  It is *not* a bridge between the two chain complexes: constructing the
degreewise comparison `Cₙ^{Task-9}(S;ℤ₂) ≅ ((SSet.singularChainComplexFunctor _).obj R).obj S`
remains `DEFERRED` exactly as in Task 10, §4.

Negative controls for the same probe (declarations that do **not** elaborate at the pin —
`SSet.homology`, `SSetPair`, `TopPair.HomologyPretheory`, `SSet.sd`,
`SSet.normalizedChainComplex`, `TopCat.Homotopy.singularChainComplexFunctorObjMap`) are
recorded verbatim in `TASK11_UPSTREAM_DELTA_AUDIT.md`, WP14; they cannot be recorded here,
since a file containing them would not compile.
-/

universe w v u

namespace SpineTask11

open CategoryTheory Limits AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- **WP14, probe A1 (pin, positive).**  The canonical chain-level comparison map
`C_*(K;R) ⟶ C_*^sing(|K|;R)`, in the generic form available in pinned Mathlib: the image of
the adjunction unit `η_K : K ⟶ Sing |K|` under the linearisation functor
`SSet.singularChainComplexFunctor`. -/
noncomputable def unitChainComplexMap (R : C) (K : SSet.{w}) :
    ((SSet.singularChainComplexFunctor C).obj R).obj K ⟶
      ((singularChainComplexFunctor C).obj R).obj (SSet.toTop.obj K) :=
  ((SSet.singularChainComplexFunctor C).obj R).map (sSetTopAdj.unit.app K)

/-- The target of `unitChainComplexMap` is the generic simplicial chain complex of the
singular simplicial set of `|K|`: singular chains of a space are, at the pin already,
*defined* as the simplicial chains of its singular simplicial set. -/
theorem unitChainComplexMap_target (R : C) (K : SSet.{w}) :
    ((singularChainComplexFunctor C).obj R).obj (SSet.toTop.obj K) =
      ((SSet.singularChainComplexFunctor C).obj R).obj
        (TopCat.toSSet.obj (SSet.toTop.obj K)) :=
  rfl

/-- **WP14, probe A2 (pin, positive).**  The comparison morphism is natural in `K`.  This is
the naturality of the adjunction unit after linearisation, and it is the strongest general
statement about this morphism available in the pinned library. -/
theorem unitChainComplexMap_naturality (R : C) {K L : SSet.{w}} (f : K ⟶ L) :
    ((SSet.singularChainComplexFunctor C).obj R).map f ≫ unitChainComplexMap R L =
      unitChainComplexMap R K ≫
        ((singularChainComplexFunctor C).obj R).map (SSet.toTop.map f) := by
  have h : f ≫ sSetTopAdj.unit.app L
      = sSetTopAdj.unit.app K ≫ TopCat.toSSet.map (SSet.toTop.map f) :=
    sSetTopAdj.unit.naturality f
  dsimp only [unitChainComplexMap]
  rw [← Functor.map_comp, h, Functor.map_comp]
  rfl

/-- **WP14, probe A3 (pin, the target of the upstream search).**  The statement that the
canonical comparison `C_*(K;R) ⟶ C_*^sing(|K|;R)` is a quasi-isomorphism.

This `Prop` is the exact shape of the theorem searched for in WP5.  It is **not proved**
here, and the audit found no proof of it — or of any statement implying it — either in the
pinned Mathlib (`v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`) or in the
audited upstream commit `076c9da2981330e0d1ba84a10afa6544faafa612`.  Nothing consumes it. -/
def UnitQuasiIsoStatement [CategoryWithHomology C] (R : C) (K : SSet.{w}) : Prop :=
  QuasiIso (unitChainComplexMap R K)

/-- **WP3/WP14 bookkeeping.**  The Task-9/Task-10 chain map and the generic Mathlib
comparison morphism are two linearisations of **one and the same** morphism of simplicial
sets, the adjunction unit at `K = N(𝓤)`.

The first component is the Task-10 identification `J = C_*(η_K)`
(`NerveGeom.chainMap_eq_unitChainMap`); the second is the definition of
`unitChainComplexMap`.  This is deliberately *not* a comparison of the two chain complexes:
that bridge stays `DEFERRED`. -/
theorem taskNine_and_mathlib_share_the_unit {X : Type w} {ι : Type w}
    (U : ι → Set X) (n : ℕ) (R : C) :
    NerveGeom.chainMap U n
        = NerveGeom.sSetChainMap (sSetTopAdj.unit.app (NerveGeom.coverNerveSSet U)) n ∧
      unitChainComplexMap R (NerveGeom.coverNerveSSet U)
        = ((SSet.singularChainComplexFunctor C).obj R).map
            (sSetTopAdj.unit.app (NerveGeom.coverNerveSSet U)) :=
  ⟨NerveGeom.chainMap_eq_unitChainMap U n, rfl⟩

end SpineTask11
