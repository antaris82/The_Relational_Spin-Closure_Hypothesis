import RequestProject.Spine.Nerve.Comparison.RelativeMap
import RequestProject.Spine.Nerve.Skeleton.Pushout
import RequestProject.Spine.Nerve.StandardCell.Pair

/-!
# The singular cell-family target map

Definitions and elementary interface only:

* `topCellPairMap X r σ` — the map of relative singular complexes
  `C_*^{sing}(|Δ[r]|,|∂Δ[r]|) ⟶ C_*^{sing}(|K^{(r)}|,|K^{(r-1)}|)` induced by the realized
  characteristic map `|cellChar X r σ|` and attaching map `|cellAttach X r σ|`;
* `tgtSumMod X r q = ⊕_{σ ∈ X.nonDegenerate r} H_q^{sing}(|Δ[r]|, |∂Δ[r]|; ℤ₂)`;
* `tgtDecomp X r q` — the singular cell-family comparison, the map out of that direct sum
  whose `σ`-component is induced by `topCellPairMap X r σ`, together with its value on a
  `Finsupp.single` (`tgtDecomp_single`).

The theorem that `tgtDecomp` is an isomorphism is `SpineTask24.isIso_tgtDecomp` in
`RequestProject.Spine.Nerve.CellFamily.TargetDecomposition`; importing the *definition* of
`tgtDecomp` does not import that proof, nor any of the standard-cell homology, excision or
generator stack it rests on.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask13
  SpineTask14 SpineTask15

universe u

namespace SpineTask22

section Cells

variable (X : SSet.{u}) (r : ℕ)

/-- **The `σ`-component on the singular side.**  The map of relative singular complexes
induced by the realized characteristic map `|cellChar X r σ|` and attaching map
`|cellAttach X r σ|`. -/
def topCellPairMap (σ : X.nonDegenerate r) :
    relChainCx (stdCellPair.{u} r) ⟶ relChainCx (singSkInc X r) :=
  relChainCxMap (stdCellPair.{u} r) (singSkInc X r)
    (TopCat.toSSet.map (SSet.toTop.map (cellAttach X r σ)))
    (TopCat.toSSet.map (SSet.toTop.map (cellChar X r σ)))
    (by
      simp only [← Functor.map_comp]
      rw [cellAttach_comm X r σ])

end Cells

section Square

variable (X : SSet.{u}) (r q : ℕ)

/-- `⊕_{σ ∈ X.nonDegenerate r} H_q^{sing}(|Δ[r]|, |∂Δ[r]|; ℤ₂)`. -/
def tgtSumMod : ModuleCat.{u} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (↑(X.nonDegenerate r) →₀ (relHomology (stdCellPair.{u} r) q))

/-- **The singular cell-family comparison.**  On the `σ`-summand it is the map induced by the
realized characteristic map of the cell of `σ`. -/
def tgtDecomp : tgtSumMod X r q ⟶ (relChainCx (singSkInc X r)).homology q :=
  ModuleCat.ofHom (Finsupp.lsum (ZMod 2)
    fun σ => (HomologicalComplex.homologyMap (topCellPairMap X r σ) q).hom)

theorem tgtDecomp_single (σ : X.nonDegenerate r) (m : relHomology (stdCellPair.{u} r) q) :
    (tgtDecomp X r q).hom (Finsupp.single σ m)
      = (HomologicalComplex.homologyMap (topCellPairMap X r σ) q).hom m := by
  show Finsupp.sum (Finsupp.single σ m)
    (fun σ m => (HomologicalComplex.homologyMap (topCellPairMap X r σ) q).hom m) = _
  exact Finsupp.sum_single_index (map_zero _)

end Square

end SpineTask22
