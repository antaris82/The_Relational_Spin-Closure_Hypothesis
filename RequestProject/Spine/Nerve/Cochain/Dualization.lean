import RequestProject.Spine.Nerve.Cochain.CochainMap
import RequestProject.Spine.AlgebraicTopology.DualCohomology

/-!
# Task 10, WP2/WP10 : explicit dualisation of `ℤ₂`-chain maps

The Spine's cochain complexes are honest function types

`Cⁿ = (n-simplices) → ℤ₂`,

and its chain complexes are the free modules `Cₙ = (n-simplices) →₀ ℤ₂`.  Over the field `ℤ₂`
the second is the *predual* of the first: `Hom_{ℤ₂}(α →₀ ℤ₂, ℤ₂) ≅ (α → ℤ₂)` naturally
(`NerveGeom.freeDualEquiv`, i.e. Mathlib's `Finsupp.llift`).  Under this identification every
`ℤ₂`-linear map of free modules has a transpose

`NerveGeom.dualOf : ((A →₀ ℤ₂) →ₗ (B →₀ ℤ₂)) → ((B → ℤ₂) →ₗ (A → ℤ₂))`,

and dualisation is an **exact, strictly contravariant, additive** operation: no universal
coefficient theorem and no exactness hypothesis is used anywhere — `dualOf` is defined by an
explicit formula and every property below is proved from it.

The point of this module is that the three Task-9 chain-level objects dualise onto the three
Task-5/6/7 cochain-level objects *on the nose*:

* `dualOf_simpBoundary` — `dualOf ∂^simp = δ_simp`;
* `dualOf_singBoundary` — `dualOf ∂^sing = δ_sing`;
* `dualOf_chainMap`     — `dualOf J = J*`, the Task-9 `geometricCochainMap`.

Hence a chain-level homotopy on the Task-9 complexes dualises to a genuine cochain-level
homotopy on the *existing* Spine cochain complexes; this is what
`RequestProject.Spine.Nerve.Cochain.ChainHomotopyComparison` consumes.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

/-! ## The predual identification and the transpose -/

/- The generic `ℤ₂`-dualisation theory lives in
`RequestProject.Spine.AlgebraicTopology.DualCohomology`, which knows nothing about nerves,
covers or geometry.  Its names are re-exported here, so `NerveGeom.dualOf` and its algebraic
properties are the generic ones, not a second copy. -/
export SpineDualCohomology (freeDualEquiv freeDualEquiv_apply freeDualEquiv_symm_apply dualOf
  dualOf_apply linearCombination_dualOf dualOf_id dualOf_comp dualOf_add dualOf_sum
  dualOf_lmapDomain)

/-! ## The Task-9 chain data dualise onto the Spine cochain data -/

variable {X : Type w} {ι : Type u}

/-- `dualOf ∂^simp = δ_simp`: the transpose of the Task-9 simplicial boundary is the Task-7
simplicial coboundary of the nerve. -/
theorem dualOf_simpBoundary (U : ι → Set X) (n : ℕ) :
    dualOf (simpBoundary U n)
      = (underlyingPresimplicial (coverNerveSSet U)).d n := by
  rw [simpBoundary, dualOf_sum]
  ext c σ
  simp only [LinearMap.coe_sum, Finset.sum_apply, dualOf_lmapDomain,
    LinearMap.funLeft_apply]
  rfl

/-- `dualOf ∂^sing = δ_sing`: the transpose of the Task-9 singular boundary is the Task-5
singular coboundary. -/
theorem dualOf_singBoundary (R : TopCat.{u}) (n : ℕ) :
    dualOf (singBoundary R n) = Mod2Cohomology.d R n := by
  rw [singBoundary, dualOf_sum]
  ext c σ
  simp only [LinearMap.coe_sum, Finset.sum_apply, dualOf_lmapDomain,
    LinearMap.funLeft_apply, Mod2Cohomology.d_apply_simplex]

/-- **`dualOf J = J*`.**  The transpose of the Task-9 chain map is *exactly* the Task-9
cochain map `geometricCochainMap`, i.e. the canonical geometric comparison used by the Spine.
Nothing new is introduced at cochain level. -/
theorem dualOf_chainMap (U : ι → Set X) (n : ℕ) :
    dualOf (chainMap U n) = (geometricCochainMap U).map n := by
  rw [chainMap, dualOf_lmapDomain]
  rfl

end NerveGeom
