import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic

/-!
# The free `ℤ₂`-linearisation of a simplicial set

This is the base of the whole Stage-1.3 chain-level development: for an arbitrary simplicial
set `S`,

* `NerveGeom.SSetChain S n = Sₙ →₀ ℤ₂` — the free `ℤ₂`-module on the `n`-simplices;
* `NerveGeom.sSetBoundary S n = ∑ᵢ (dᵢ)_*` — the (unsigned, because `-1 = 1` in `ℤ₂`)
  boundary;
* `NerveGeom.sSetChainMap φ n = (φₙ)_*` — the linearisation of a simplicial map;
* `NerveGeom.sSetBoundary_naturality` — linearisation is a functor into `ℤ₂`-chain complexes:
  every simplicial map commutes with the linearised boundaries.  Only the naturality of `φ`
  is used.

Nothing here mentions a cover, a nerve or a realization: the module is generic simplicial
homological algebra and sits below every Nerve-specific layer.  The identification of the
project's Task-9 nerve data with this construction is
`RequestProject.Spine.Nerve.Basic.UnitChainMap`.

The declarations keep their historical `NerveGeom` namespace so that no downstream statement
had to be edited when the generic half was separated from the Nerve-specific half.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite SimplexCategory

universe u

/-! ## Free `ℤ₂`-linearisation of a simplicial set -/

/-- Degree-`n` free `ℤ₂`-chains of a simplicial set `S`: the free `ℤ₂`-module on `Sₙ`. -/
abbrev SSetChain (S : SSet.{u}) (n : ℕ) : Type u :=
  (S.obj (op (SimplexCategory.mk n))) →₀ ZMod 2

/-- The linearised boundary `∂ = ∑ᵢ (dᵢ)_*` of a simplicial set (unsigned: `-1 = 1` in
`ℤ₂`). -/
def sSetBoundary (S : SSet.{u}) (n : ℕ) : SSetChain S (n + 1) →ₗ[ZMod 2] SSetChain S n :=
  ∑ i : Fin (n + 2), Finsupp.lmapDomain (ZMod 2) (ZMod 2) (S.δ i)

/-- The linearisation of a morphism of simplicial sets. -/
def sSetChainMap {S T : SSet.{u}} (φ : S ⟶ T) (n : ℕ) :
    SSetChain S n →ₗ[ZMod 2] SSetChain T n :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (φ.app (op (SimplexCategory.mk n)))

@[simp] theorem sSetBoundary_single {S : SSet.{u}} {n : ℕ}
    (σ : S.obj (op (SimplexCategory.mk (n + 1)))) (c : ZMod 2) :
    sSetBoundary S n (Finsupp.single σ c)
      = ∑ i : Fin (n + 2), Finsupp.single (S.δ i σ) c := by
  simp [sSetBoundary, LinearMap.sum_apply, Finsupp.mapDomain_single]

@[simp] theorem sSetChainMap_single {S T : SSet.{u}} (φ : S ⟶ T) {n : ℕ}
    (σ : S.obj (op (SimplexCategory.mk n))) (c : ZMod 2) :
    sSetChainMap φ n (Finsupp.single σ c)
      = Finsupp.single (φ.app (op (SimplexCategory.mk n)) σ) c := by
  simp [sSetChainMap, Finsupp.mapDomain_single]

/-- **Functoriality.**  Linearisation lands in chain complexes: a morphism of simplicial
sets commutes with the linearised boundaries.  Only the naturality of `φ` is used. -/
theorem sSetBoundary_naturality {S T : SSet.{u}} (φ : S ⟶ T) (n : ℕ) :
    (sSetChainMap φ n).comp (sSetBoundary S n)
      = (sSetBoundary T n).comp (sSetChainMap φ (n + 1)) := by
  refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, sSetChainMap_single,
    sSetBoundary_single, map_sum, sSetChainMap_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrFun (φ.naturality (SimplexCategory.δ i).op) σ
  exact congrArg (fun x => Finsupp.single x (1 : ZMod 2)) h

end NerveGeom
