import RequestProject.Spine.AlgebraicTopology.DirectSumHomology
import RequestProject.Spine.AlgebraicTopology.FamilyChainMap
import RequestProject.Spine.Nerve.CellFamily.SingularFactorization

/-!
# The relative cell-sum chain isomorphism

The chain-level half of the finite cell decomposition.  Everything geometric is inherited from
`RequestProject.Spine.Nerve.CellFamily.SingularFactorization`: the unique factorisation of a
singular simplex of the union of the open cells through exactly one cell
(`SpineTask23.bijective_cellSingMap`) and the relative range criterion
(`SpineTask23.cellSingMap_mem_range_incInterU_iff`).  Everything algebraic is inherited from
the generic modules `AlgebraicTopology.DirectSumComplex` and
`AlgebraicTopology.FamilyChainMap`.

## Contents

* `thetaAbs X r` — **Θ_abs**, the chain-complex isomorphism
  `⊕_{σ ∈ X.nonDegenerate r} C_*^{sing}(Δ°) ≅ C_*^{sing}(U)`;
* `thetaRel X r` — **Θ_rel**, the chain-complex isomorphism
  `⊕_{σ ∈ X.nonDegenerate r} C_*^{sing}(Δ°, Δ° \ {b_r}) ≅ C_*^{sing}(U, U ∩ V)`;
* `cellRelPairMap X r σ` — its `σ`-component, the map of relative singular complexes induced by
  the open-cell inclusion `cellIncl X r σ`;
* `sumCellHomology X r q` and `isIso_sumCellHomology` — **the relative homology
  decomposition** `⊕_σ H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(U, U ∩ V)`, for an arbitrary
  family of cells.

No finiteness of the cell family is used anywhere, and no new topology is introduced.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet NerveGeom SpineTask13 SpineTask14
  SpineTask15 SpineTask18 SpineTask23

universe u

namespace SpineTask24

/-! ## The cell family -/

section Cells

variable (X : SSet.{u}) (r : ℕ)

/-- The `σ`-th open cell inclusion of *pairs*: `Δ° ∩ (Δ° \ {b_r}) ⟶ U ∩ V`. -/
def cellInclInterMap (σ : X.nonDegenerate r) :
    SpineTask18.subTop (openStdCell.{u} r ∩ puncturedCell.{u} r) ⟶
      SpineTask18.subTop (openCells X r ∩ puncturedNbhd X r) :=
  TopCat.ofHom
    { toFun := fun x => ⟨cellPt X r σ x.1, cellPt_mem_openCells X r x.2.1,
        fun hb => x.2.2 ((cellPt_mem_barySet_iff X r σ x.1).1 hb)⟩
      continuous_toFun :=
        (((continuous_cellPt X r σ).comp continuous_subtype_val).subtype_mk _) }

theorem cellInclInter_square (σ : X.nonDegenerate r) :
    SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r) ≫ cellInclMap X r σ
      = cellInclInterMap X r σ ≫
        SpineTask18.incInterU (openCells X r) (puncturedNbhd X r) := by
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  exact Subtype.ext rfl

/-- The family of simplicial maps `Sing Δ° ⟶ Sing U`, one for each cell. -/
abbrev cellSSetMap (σ : X.nonDegenerate r) :
    TopCat.toSSet.obj (SpineTask18.subTop (openStdCell.{u} r)) ⟶
      TopCat.toSSet.obj (SpineTask18.subTop (openCells X r)) :=
  TopCat.toSSet.map (cellInclMap X r σ)

/-- The family of simplicial maps of the subobjects. -/
abbrev cellSSetInterMap (σ : X.nonDegenerate r) :
    TopCat.toSSet.obj (SpineTask18.subTop (openStdCell.{u} r ∩ puncturedCell.{u} r)) ⟶
      TopCat.toSSet.obj (SpineTask18.subTop (openCells X r ∩ puncturedNbhd X r)) :=
  TopCat.toSSet.map (cellInclInterMap X r σ)

theorem cellSSet_square (σ : X.nonDegenerate r) :
    TopCat.toSSet.map (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))
        ≫ cellSSetMap X r σ
      = cellSSetInterMap X r σ
        ≫ TopCat.toSSet.map
          (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r)) := by
  rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, cellInclInter_square]

/-- The total map on `q`-simplices of the cell family **is** the Task-23 `cellSingMap`. -/
theorem famSimp_cellSSetMap (q : ℕ) :
    famSimp (cellSSetMap X r) q = cellSingMap X r q := rfl

theorem bijective_famSimp_cell (q : ℕ) : Function.Bijective (famSimp (cellSSetMap X r) q) :=
  bijective_cellSingMap X r q

/-- **Θ_abs.**  The absolute cell-sum comparison
`⊕_{σ} C_*^{sing}(Δ°) ⟶ C_*^{sing}(U)`. -/
def thetaAbs : finsuppCx ↑(X.nonDegenerate r)
      (sSetChainComplexFunctor.obj (TopCat.toSSet.obj
        (SpineTask18.subTop (openStdCell.{u} r))))
    ⟶ sSetChainComplexFunctor.obj (TopCat.toSSet.obj
        (SpineTask18.subTop (openCells X r))) :=
  famChainMap (cellSSetMap X r)

/-- **WP2.**  `Θ_abs` is an isomorphism of chain complexes. -/
instance isIso_thetaAbs : IsIso (thetaAbs X r) :=
  isIso_famChainMap _ (bijective_famSimp_cell X r)

/-- The `σ`-component of `Θ_rel`: the map of relative singular complexes induced by the open
cell inclusion `cellIncl X r σ`. -/
def cellRelPairMap (σ : X.nonDegenerate r) :
    relSingChainCx (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))
      ⟶ relSingChainCx (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r)) :=
  relChainCxMap _ _ (cellSSetInterMap X r σ) (cellSSetMap X r σ) (cellSSet_square X r σ)

/-- **Θ_rel.**  The relative cell-sum comparison
`⊕_{σ} C_*^{sing}(Δ°, Δ° \ {b_r}) ⟶ C_*^{sing}(U, U ∩ V)`. -/
def thetaRel : finsuppCx ↑(X.nonDegenerate r)
      (relSingChainCx (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r)))
    ⟶ relSingChainCx (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r)) :=
  famRelChainMap _ _ (cellSSetMap X r) (cellSSetInterMap X r) (cellSSet_square X r)

theorem finsuppCxι_thetaRel (σ : X.nonDegenerate r) :
    finsuppCxι _ _ σ ≫ thetaRel X r = cellRelPairMap X r σ :=
  finsuppCxι_desc _ σ

/-- **WP3.**  `Θ_rel` is an isomorphism of chain complexes.  The relative half of the input is
exactly the Task-23 range criterion `cellSingMap_mem_range_incInterU_iff`. -/
instance isIso_thetaRel : IsIso (thetaRel X r) :=
  isIso_famRelChainMap _ _ _ _ _
    (toSSet_map_injective _ (SpineTask18.incInterU_injective _ _))
    (toSSet_map_injective _ (SpineTask18.incInterU_injective _ _))
    (bijective_famSimp_cell X r)
    (fun q σ s => cellSingMap_mem_range_incInterU_iff X r q σ s)

/-! ## The relative homology decomposition -/

variable (q : ℕ)

/-- The comparison
`⊕_{σ} H_q^{sing}(Δ°, Δ° \ {b_r}) ⟶ H_q^{sing}(U, U ∩ V)`,
whose `σ`-component is the map induced by the open cell inclusion. -/
def sumCellHomology :
    ModuleCat.of (ZMod 2) (↑(X.nonDegenerate r) →₀
      ↥((relSingChainCx
        (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).homology q))
      ⟶ (relSingChainCx
        (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r))).homology q :=
  sumHomologyMap (fun σ => finsuppCxι _ _ σ ≫ thetaRel X r) q

theorem sumCellHomology_single (σ : X.nonDegenerate r)
    (m : ↥((relSingChainCx
      (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).homology q)) :
    (sumCellHomology X r q).hom (Finsupp.single σ m)
      = (HomologicalComplex.homologyMap (cellRelPairMap X r σ) q).hom m := by
  rw [sumCellHomology, sumHomologyMap_single, finsuppCxι_thetaRel]

/-- **The relative homology decomposition.**
`⊕_{σ ∈ X.nonDegenerate r} H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(U, U ∩ V)` for an arbitrary
family of cells: the chain-level isomorphism `Θ_rel` identifies the target with the direct sum
of the standard-cell complexes, and the homology of a direct sum is the direct sum of the
homology by `SpineTask23.isIso_sumHomologyMap_of_iso`. -/
theorem isIso_sumCellHomology : IsIso (sumCellHomology X r q) :=
  isIso_sumHomologyMap_of_iso (thetaRel X r) q

end Cells

end SpineTask24
