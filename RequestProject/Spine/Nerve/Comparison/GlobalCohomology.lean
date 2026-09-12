import RequestProject.Spine.Nerve.Comparison.GlobalHomology
import RequestProject.Spine.Nerve.Cochain.ComparisonSpec
import RequestProject.Spine.Nerve.Cochain.Dualization

/-!
# The canonical geometric comparison on cohomology

The global homology comparison `NerveComparison.globalHomologyIso` says that the frozen
canonical chain map `J = C_*(η)` is a homology isomorphism for *every* simplicial set.  For the
cover nerve `K = N(𝓤)` that chain map is, on the nose, the Task-9 map `NerveGeom.chainMap`
(`NerveGeom.chainMap_eq_unitChainMap`), whose transpose is the frozen cochain comparison
`NerveGeom.geometricCochainMap` (`NerveGeom.dualOf_chainMap`).

Over the field `ℤ₂` the transpose of a homology isomorphism of free complexes is a cohomology
isomorphism (`SpineDualCohomology.bijective_Hmap`).  Combining the two gives the endpoint

`NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂)` **is bijective**,

hence `NerveGeom.GeometricComparison 𝓤` unconditionally.  No chain homotopy equivalence, no
finiteness, no good-cover hypothesis and no Nerve Theorem is used, and no map is replaced.
-/

noncomputable section

open CategoryTheory Opposite CechZ2 SimplexCategory

universe u

namespace NerveGeom

variable {X : Type u} {ι : Type u}

/-- The two Task-9 boundaries square to zero: they are the linearised simplicial boundaries. -/
theorem simpBoundary_comp_simpBoundary (U : ι → Set X) (n : ℕ) :
    (simpBoundary U n).comp (simpBoundary U (n + 1)) = 0 :=
  SpineTask13.sSetBoundary_comp_sSetBoundary (coverNerveSSet U) n

theorem singBoundary_comp_singBoundary (R : TopCat.{u}) (n : ℕ) :
    (singBoundary R n).comp (singBoundary R (n + 1)) = 0 :=
  SpineTask13.sSetBoundary_comp_sSetBoundary (TopCat.toSSet.obj R) n

/-- **The chain-level comparison for the nerve is a homology isomorphism**, in the elementary
(submodule-quotient) formulation: this is the global comparison `NerveComparison.globalHomologyIso`
for the simplicial set `N(𝓤)`, read through the identification of the Task-9 chain data with the
canonical chain complex functor. -/
theorem bijective_naive_homologyMap (U : ι → Set X) (n : ℕ) :
    Function.Bijective
      (SpineNaiveHomology.homologyMap
        (M := SpineDualCohomology.FreeMod (fun m => Nerve U m))
        (N := SpineDualCohomology.FreeMod
          (fun m => Mod2Cohomology.Simplex (coverNerveRealization U) m))
        (simpBoundary U) (singBoundary (coverNerveRealization U)) (chainMap U)
        (chainMap_comm U) n) :=
  SpineNaiveHomology.bijective_homologyMap_of_isIso
    (K := SpineTask14.sSetChainComplexFunctor.obj (coverNerveSSet U))
    (L := SpineTask14.sSetChainComplexFunctor.obj
      (TopCat.toSSet.obj (SSet.toTop.obj (coverNerveSSet U))))
    (SpineTask14.sSetChainComplexFunctor.map (sSetTopAdj.unit.app (coverNerveSSet U)))
    (simpBoundary U) (singBoundary (coverNerveRealization U)) (chainMap U)
    (fun m => (SpineTask14.sSetChainComplexFunctor_d (coverNerveSSet U) m).symm)
    (fun m => (SpineTask14.sSetChainComplexFunctor_d
      (TopCat.toSSet.obj (SSet.toTop.obj (coverNerveSSet U))) m).symm)
    (fun _ => rfl) (chainMap_comm U) n
    (NerveComparison.globalHomologyIso (coverNerveSSet U) n)

/-- **The canonical geometric comparison is bijective in every degree.** -/
theorem geometricHmap_bijective (U : ι → Set X) (n : ℕ) :
    Function.Bijective (geometricHmap U n) := by
  have hH : Function.Bijective ((geometricCochainMap U).Hmap n) :=
    SpineDualCohomology.bijective_Hmap
      (α := fun m => Nerve U m)
      (β := fun m => Mod2Cohomology.Simplex (coverNerveRealization U) m)
      (δ := (underlyingPresimplicial (coverNerveSSet U)).d)
      (ε := Mod2Cohomology.d (coverNerveRealization U))
      (BdA := (underlyingPresimplicial (coverNerveSSet U)).coboundaries)
      (BdB := Mod2Cohomology.coboundaries (coverNerveRealization U))
      (φ := (geometricCochainMap U).map)
      (dA := simpBoundary U) (dB := singBoundary (coverNerveRealization U))
      (f := chainMap U)
      ((geometricCochainMap U).comm) rfl (fun _ => rfl) rfl (fun _ => rfl)
      (chainMap_comm U) (singBoundary_comp_singBoundary (coverNerveRealization U))
      (fun m => (dualOf_simpBoundary U m).symm)
      (fun m => (dualOf_singBoundary (coverNerveRealization U) m).symm)
      (fun m => (dualOf_chainMap U m).symm)
      (bijective_naive_homologyMap U) n
  exact (cechCohomologyEquivSSet U n).bijective.comp hH

/-- **The unconditional canonical cohomological comparison.** -/
def geometricComparison (U : ι → Set X) : GeometricComparison U where
  bijective := geometricHmap_bijective U

end NerveGeom
