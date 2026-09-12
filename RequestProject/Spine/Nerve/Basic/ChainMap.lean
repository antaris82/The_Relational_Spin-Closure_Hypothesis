import RequestProject.Spine.Nerve.Basic.Realization

/-!
# Task 9, WP6 : the simplicial-to-singular **chain** map

The Task-5/Task-6 layers of the Spine are cochain-level theories.  For WP6 the corresponding
chain level is made explicit: with `ℤ₂` coefficients, the free module on a set of simplices is
the `Finsupp` module, the boundary is the (unsigned, because `-1 = 1` in `ℤ₂`) sum of the face
maps, and

`Jₙ : Cₙ^simp(N(𝓤);ℤ₂) → Cₙ^sing(|N(𝓤)|;ℤ₂)`

is the linear extension of the *canonical characteristic simplex* `σ ↦ |σ|` of WP5.  No other
singular simplex is used anywhere.

The theorem `chainMap_comm`, `∂_sing ∘ J = J ∘ ∂_simp`, consumes exactly the face-compatibility
result `NerveGeom.charSimplex_face` of WP5; nothing is postulated.

Degeneracies are **not** quotiented out: the Task-6 complex is the unnormalized one (WP3), so
`J` is defined on all of `Cₙ^simp` and no descent through a normalization is needed or claimed.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

variable {X : Type w} {ι : Type u}

/-! ## Chains -/

/-- Simplicial `ℤ₂`-chains of the cover nerve: the free `ℤ₂`-module on the nerve simplices. -/
abbrev SimpChain (U : ι → Set X) (n : ℕ) : Type u := Nerve U n →₀ ZMod 2

/-- Singular `ℤ₂`-chains of a space: the free `ℤ₂`-module on the singular simplices. -/
abbrev SingChain (R : TopCat.{u}) (n : ℕ) : Type u := Mod2Cohomology.Simplex R n →₀ ZMod 2

/-- The simplicial boundary `∂ = ∑ₜ dₜ` (unsigned: `-1 = 1` in `ℤ₂`). -/
def simpBoundary (U : ι → Set X) (n : ℕ) : SimpChain U (n + 1) →ₗ[ZMod 2] SimpChain U n :=
  ∑ t : Fin (n + 2), Finsupp.lmapDomain (ZMod 2) (ZMod 2) (CechZ2.face t)

/-- The singular boundary `∂ = ∑ᵢ ∂ᵢ` (unsigned: `-1 = 1` in `ℤ₂`). -/
def singBoundary (R : TopCat.{u}) (n : ℕ) : SingChain R (n + 1) →ₗ[ZMod 2] SingChain R n :=
  ∑ i : Fin (n + 2), Finsupp.lmapDomain (ZMod 2) (ZMod 2) (Mod2Cohomology.face i)

@[simp] theorem simpBoundary_single {U : ι → Set X} {n : ℕ} (σ : Nerve U (n + 1))
    (c : ZMod 2) :
    simpBoundary U n (Finsupp.single σ c)
      = ∑ t : Fin (n + 2), Finsupp.single (CechZ2.face t σ) c := by
  simp [simpBoundary, LinearMap.sum_apply, Finsupp.mapDomain_single]

@[simp] theorem singBoundary_single {R : TopCat.{u}} {n : ℕ}
    (s : Mod2Cohomology.Simplex R (n + 1)) (c : ZMod 2) :
    singBoundary R n (Finsupp.single s c)
      = ∑ i : Fin (n + 2), Finsupp.single (Mod2Cohomology.face i s) c := by
  simp [singBoundary, LinearMap.sum_apply, Finsupp.mapDomain_single]

/-! ## The chain map -/

/-- **WP6.  The simplicial-to-singular chain map** `Jₙ`, the linear extension of the canonical
geometric characteristic simplex `σ ↦ |σ|`. -/
def chainMap (U : ι → Set X) (n : ℕ) :
    SimpChain U n →ₗ[ZMod 2] SingChain (coverNerveRealization U) n :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (charSimplex U n)

@[simp] theorem chainMap_single {U : ι → Set X} {n : ℕ} (σ : Nerve U n) (c : ZMod 2) :
    chainMap U n (Finsupp.single σ c) = Finsupp.single (charSimplex U n σ) c := by
  simp [chainMap, Finsupp.mapDomain_single]

/-- **WP6, principal: `∂_sing ∘ J = J ∘ ∂_simp`.**

The proof consumes the WP5 face-compatibility theorem `charSimplex_face` and nothing else. -/
theorem chainMap_comm (U : ι → Set X) (n : ℕ) :
    (singBoundary (coverNerveRealization U) n).comp (chainMap U (n + 1))
      = (chainMap U n).comp (simpBoundary U n) := by
  refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, chainMap_single,
    singBoundary_single, simpBoundary_single, map_sum, chainMap_single]
  exact Finset.sum_congr rfl fun i _ => by rw [charSimplex_face]

theorem chainMap_comm_apply (U : ι → Set X) (n : ℕ) (x : SimpChain U (n + 1)) :
    singBoundary (coverNerveRealization U) n (chainMap U (n + 1) x)
      = chainMap U n (simpBoundary U n x) :=
  congrFun (congrArg DFunLike.coe (chainMap_comm U n)) x

end NerveGeom
