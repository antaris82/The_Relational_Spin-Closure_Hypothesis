import RequestProject.Spine.AlgebraicTopology.RelativeLES
import RequestProject.Spine.AlgebraicTopology.SimplicialSkeleton

/-!
# Task 14, WP4 and WP12 : realization of colimits, and the canonical relative comparison

## What realization carries across

`SSet.toTop` is a left adjoint, hence preserves all colimits; that generic fact and its
consequence for pushout squares are `SpineTask14.realizationPreservesColimits` and
`SpineTask14.toTop_isPushout` in
`RequestProject.Spine.AlgebraicTopology.RealizationColimits`.

## WP12 — the relative comparison induced by `J = C_*(η_K)`

The canonical comparison is frozen: `J = C_*(η)` where `η` is the unit of
`SSet.toTop ⊣ TopCat.toSSet`.  Because `η` is *natural*, the square

```
K^{(r-1)} ──η──▶ Sing|K^{(r-1)}|
   │                  │
   ▼                  ▼
K^{(r)}   ──η──▶ Sing|K^{(r)}|
```

commutes on the nose, so the WP7 functoriality produces a comparison of **relative** complexes

`relJ X r : C_*(K^{(r)},K^{(r-1)}) ⟶ C_*^{sing}(|K^{(r)}|,|K^{(r-1)}|)`

which is induced by `J` and by nothing else (`relJ_tau₂`).  `relJ_generator` proves that on the
class of a simplex `σ` it is the class of the **characteristic singular simplex of `σ`**, i.e.
`η(σ)`, as WP12 demands.

## What is *not* here

`relJ` is a chain map unconditionally, but the relative singular *long exact sequence* of the
realized pair needs the singular chains of `|K^{(r-1)}|` to inject into those of `|K^{(r)}|`,
i.e. needs `|K^{(r-1)}| → |K^{(r)}|` to be injective.  That statement — *geometric realization
of a monomorphism of simplicial sets is injective* — is **not** in the pinned Mathlib; it is
recorded as `RealizationInjective` below and carried as an explicit hypothesis wherever it is
used.  See `TASK14_SPECIALIZED_CELL_ATTACHMENT.md`, blocker **B2**.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology NerveGeom SpineTask13

universe u

namespace SpineTask14

/-! The realization-preserves-colimits half of this module is generic and lives in
`RequestProject.Spine.AlgebraicTopology.RealizationColimits`. -/

/-! ## WP12 : the canonical relative comparison -/

variable (X : SSet.{u}) (r : ℕ)

/-- The singular simplicial set of the realization of the `r`-skeleton. -/
abbrev SingSk : SSet.{u} := TopCat.toSSet.obj (SSet.toTop.obj (Sk X r))

/-- The map `Sing|K^{(r-1)}| ⟶ Sing|K^{(r)}|` induced by the realized skeletal inclusion. -/
abbrev singSkInc : SingSk X r ⟶ SingSk X (r + 1) :=
  TopCat.toSSet.map (SSet.toTop.map (skInc X r))

/-- **The naturality square of the frozen canonical map `η`** for the skeletal pair. -/
theorem unit_skeletal_square :
    skInc X r ≫ sSetTopAdj.unit.app (Sk X (r + 1))
      = sSetTopAdj.unit.app (Sk X r) ≫ singSkInc X r :=
  sSetTopAdj.unit.naturality (skInc X r)

/-- **WP12.  The relative comparison map induced by `J = C_*(η)`**,

`J^rel_r : C_*(K^{(r)}, K^{(r-1)}) ⟶ C_*^{sing}(|K^{(r)}|, |K^{(r-1)}|)`.

It is obtained from the WP7 functoriality applied to the *naturality square of the unit*; no
other map is chosen anywhere. -/
def relJ : relChainCx (skInc X r) ⟶ relChainCx (singSkInc X r) :=
  relChainCxMap (skInc X r) (singSkInc X r) (sSetTopAdj.unit.app (Sk X r))
    (sSetTopAdj.unit.app (Sk X (r + 1))) (unit_skeletal_square X r)

/-- The morphism of short exact sequences carrying `relJ`. -/
def relJSC : relSC (skInc X r) ⟶ relSC (singSkInc X r) :=
  relSCMap (skInc X r) (singSkInc X r) (sSetTopAdj.unit.app (Sk X r))
    (sSetTopAdj.unit.app (Sk X (r + 1))) (unit_skeletal_square X r)

/-- **The middle component of the comparison is literally `J = C_*(η)`.** -/
theorem relJ_tau₂ :
    (relJSC X r).τ₂ = sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X (r + 1))) := rfl

/-- **The third component of the comparison is `relJ`.** -/
theorem relJ_tau₃ : (relJSC X r).τ₃ = relJ X r := rfl

/-- The **characteristic singular simplex** of a simplex of the `r`-skeleton: the value of the
canonical unit `η` on it. -/
abbrev charSimplexSk {q : ℕ} (σ : (Sk X (r + 1)).obj (op (SimplexCategory.mk q))) :
    (SingSk X (r + 1)).obj (op (SimplexCategory.mk q)) :=
  (sSetTopAdj.unit.app (Sk X (r + 1))).app (op (SimplexCategory.mk q)) σ

/-- **WP12, the generator identification.**  On the relative class of a simplex `σ` the
comparison `J^rel` is the relative class of the **characteristic singular simplex of `σ`**. -/
theorem relJ_generator {q : ℕ} (σ : (Sk X (r + 1)).obj (op (SimplexCategory.mk q)))
    (c : ZMod 2) :
    ((relJ X r).f q).hom (Submodule.Quotient.mk (Finsupp.single σ c))
      = Submodule.Quotient.mk (Finsupp.single (charSimplexSk X r σ) c) := by
  show Submodule.Quotient.mk
      (sSetChainMap (sSetTopAdj.unit.app (Sk X (r + 1))) q (Finsupp.single σ c)) = _
  rw [sSetChainMap_single]

/-! ## WP12/WP13 : the one-skeleton-step comparison, and what it still needs -/

/-- **The missing topological input `B2`**: geometric realization of the skeletal inclusion is
injective on singular simplices.  Equivalently `|K^{(r-1)}| → |K^{(r)}|` is injective.  This is
*not* provable from the pinned Mathlib; it is carried as an explicit hypothesis. -/
def RealizationInjective (X : SSet.{u}) (r : ℕ) : Prop :=
  ∀ n, Function.Injective ((singSkInc X r).app n)

/-- **WP13, the one-skeleton-step comparison theorem.**

If

* the singular chains of `|K^{(r-1)}|` inject into those of `|K^{(r)}|` (`hinj`, blocker `B2`),
* `J` is a homology isomorphism on the `(r-1)`-skeleton (`h₁`),
* the relative comparison `J^rel` is a homology isomorphism (`h₃`, the WP11 target),

then `J` is a homology isomorphism on the `r`-skeleton.

The proof is the five lemma `isIso_homologyMap_τ₂` applied to the morphism `relJSC` of the two
pair sequences; the vertical maps are the canonical `J`'s and nothing else. -/
theorem oneSkeletonStep (hinj : RealizationInjective X r)
    (h₁ : ∀ q, IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X r))) q))
    (h₃ : ∀ q, IsIso (HomologicalComplex.homologyMap (relJ X r) q)) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X (r + 1)))) q) := by
  have hstep := isIso_homologyMap_τ₂ (relJSC X r)
    (relSC_shortExact _ (subcomplex_homOfLE_injective (X.skeleton.monotone (Nat.le_succ r))))
    (relSC_shortExact _ hinj) h₁ h₃ q
  exact hstep

end SpineTask14
