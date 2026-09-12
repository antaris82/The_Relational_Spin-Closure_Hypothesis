import RequestProject.Spine.AlgebraicTopology.RelativeChainCalculus
import RequestProject.Spine.Nerve.CellFamily.RelativeChainDecomposition
import RequestProject.Spine.Nerve.CellFamily.TargetMap
import RequestProject.Spine.Nerve.StandardCell.Excision

/-!
# The singular cell-family target decomposition

The relative homology decomposition

`⊕_{σ ∈ X.nonDegenerate r} H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(U, U ∩ V)`

of `RequestProject.Spine.Nerve.CellFamily.RelativeChainDecomposition`, whose `σ`-component is
induced by the open-cell inclusion `cellIncl X r σ`, is here transported along the two excision
isomorphisms `stdCellIso` and `cellPairIso` and identified with the frozen comparison
`tgtDecomp`.  This module

* transports the decomposition (`cell_decomposition_square`), the essential point being that
  the two composites of *pair maps* involved coincide, because
  `subInc Δ° ≫ |cellChar X r σ| = cellIncl X r σ ≫ subInc U` as maps of spaces;
* proves that the resulting comparison **is** the frozen `tgtDecomp` (`mapRangeStd_tgtDecomp`);
* deduces `isIso_tgtDecomp : IsIso (tgtDecomp X r q)`, for an arbitrary family of cells, with
  `isIso_tgtDecomp_finite` retained as the finite-family wrapper.

Blocker B3 itself, `relJIsIso`, is the join module
`RequestProject.Spine.Nerve.Comparison.RelJ`.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet NerveGeom SpineTask13 SpineTask14
  SpineTask15 SpineTask18 SpineTask22 SpineTask23

universe u

namespace SpineTask24

section Compare

variable (X : SSet.{u}) (r : ℕ)

/-! ## The cell map of the punctured pairs -/

/-- The realized characteristic map, as a map `|Δ[r]| \ {b_r} ⟶ Y \ B`. -/
def stdToNbhdMap (σ : X.nonDegenerate r) :
    SpineTask18.subTop (puncturedCell.{u} r) ⟶ SpineTask18.subTop (puncturedNbhd X r) :=
  TopCat.ofHom
    { toFun := fun x => ⟨cellPt X r σ x.1, fun hb => x.2 ((cellPt_mem_barySet_iff X r σ x.1).1 hb)⟩
      continuous_toFun :=
        ((continuous_cellPt X r σ).comp continuous_subtype_val).subtype_mk _ }

theorem subInc_cellChar (σ : X.nonDegenerate r) :
    SpineTask18.subInc (openStdCell.{u} r) ≫ SSet.toTop.map (cellChar X r σ)
      = cellInclMap X r σ ≫ SpineTask18.subInc (openCells X r) := by
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  exact (cellPt_eq X r σ x.1).symm

theorem subInc_puncturedCell_square (σ : X.nonDegenerate r) :
    SpineTask18.subInc (puncturedCell.{u} r) ≫ SSet.toTop.map (cellChar X r σ)
      = stdToNbhdMap X r σ ≫ SpineTask18.subInc (puncturedNbhd X r) := by
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  exact (cellPt_eq X r σ x.1).symm

/-- The map of pairs `(|Δ[r]|, |Δ[r]| \ {b_r}) ⟶ (Y, Y \ B)` induced by the realized
characteristic map of the cell of `σ`. -/
def cellVPairMap (σ : X.nonDegenerate r) :
    relSingChainCx (SpineTask18.subInc (puncturedCell.{u} r))
      ⟶ relSingChainCx (SpineTask18.subInc (puncturedNbhd X r)) :=
  relChainCxMap _ _ (TopCat.toSSet.map (stdToNbhdMap X r σ))
    (TopCat.toSSet.map (SSet.toTop.map (cellChar X r σ)))
    (by rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, subInc_puncturedCell_square])

/-! ## The two chain-level squares -/

/-- **The excision square.**  Excising the boundary commutes with the cell inclusion. -/
theorem excision_cell_square (σ : X.nonDegenerate r) :
    SpineTask18.excisionMap (openStdCell.{u} r) (puncturedCell.{u} r) ≫ cellVPairMap X r σ
      = cellRelPairMap X r σ
        ≫ SpineTask18.excisionMap (openCells X r) (puncturedNbhd X r) := by
  rw [SpineTask18.excisionMap, cellVPairMap, relChainCxMap_comp, cellRelPairMap,
    SpineTask18.excisionMap, relChainCxMap_comp]
  refine relChainCxMap_eq_of_v _ _ ?_
  rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, subInc_cellChar]

/-- **The homotopy square.**  Replacing the boundary by the punctured cell commutes with the
cell inclusion. -/
theorem stdPair_cell_square (σ : X.nonDegenerate r) :
    stdPairMap.{u} r ≫ cellVPairMap X r σ
      = topCellPairMap X r σ ≫ pairAV X r := by
  rw [stdPairMap, cellVPairMap, relChainCxMap_comp, topCellPairMap, pairAV,
    relChainCxMap_comp]
  refine relChainCxMap_eq_of_v _ _ ?_
  rw [Category.id_comp, Category.comp_id]

/-! ## The homology square -/

variable (q : ℕ)

theorem homology_stdPair_cell_square (σ : X.nonDegenerate r) :
    (stdPairIso.{u} r q).hom
        ≫ HomologicalComplex.homologyMap (cellVPairMap X r σ) q
      = HomologicalComplex.homologyMap (topCellPairMap X r σ) q ≫ (pairAVIso X r q).hom := by
  show HomologicalComplex.homologyMap (stdPairMap.{u} r) q ≫ _
    = _ ≫ HomologicalComplex.homologyMap (pairAV X r) q
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    stdPair_cell_square]

theorem homology_excision_cell_square (σ : X.nonDegenerate r) :
    (stdExcisionIso.{u} r q).hom
        ≫ HomologicalComplex.homologyMap (cellVPairMap X r σ) q
      = HomologicalComplex.homologyMap (cellRelPairMap X r σ) q
        ≫ (excisionIsoCells X r q).hom := by
  show HomologicalComplex.homologyMap
      (SpineTask18.excisionMap (openStdCell.{u} r) (puncturedCell.{u} r)) q ≫ _
    = _ ≫ HomologicalComplex.homologyMap
      (SpineTask18.excisionMap (openCells X r) (puncturedNbhd X r)) q
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    excision_cell_square]

/-- **The transport square.**  The `σ`-component of the finite relative decomposition,
transported along the two Task-23 excision isomorphisms, is the map induced by the realized
characteristic map of the cell of `σ` — that is, the `σ`-component of `tgtDecomp`. -/
theorem cell_decomposition_square (σ : X.nonDegenerate r) :
    (stdCellIso.{u} r q).hom ≫ HomologicalComplex.homologyMap (topCellPairMap X r σ) q
      = HomologicalComplex.homologyMap (cellRelPairMap X r σ) q ≫ (cellPairIso X r q).hom := by
  have h2 : (stdPairIso.{u} r q).inv
        ≫ HomologicalComplex.homologyMap (topCellPairMap X r σ) q
      = HomologicalComplex.homologyMap (cellVPairMap X r σ) q ≫ (pairAVIso X r q).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (homology_stdPair_cell_square X r q σ).symm
  calc (stdCellIso.{u} r q).hom ≫ HomologicalComplex.homologyMap (topCellPairMap X r σ) q
      = (stdExcisionIso.{u} r q).hom ≫ ((stdPairIso.{u} r q).inv
          ≫ HomologicalComplex.homologyMap (topCellPairMap X r σ) q) := by
        rw [stdCellIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = (stdExcisionIso.{u} r q).hom ≫ (HomologicalComplex.homologyMap (cellVPairMap X r σ) q
          ≫ (pairAVIso X r q).inv) := by rw [h2]
    _ = ((stdExcisionIso.{u} r q).hom
          ≫ HomologicalComplex.homologyMap (cellVPairMap X r σ) q) ≫ (pairAVIso X r q).inv := by
        rw [Category.assoc]
    _ = (HomologicalComplex.homologyMap (cellRelPairMap X r σ) q ≫ (excisionIsoCells X r q).hom)
          ≫ (pairAVIso X r q).inv := by rw [homology_excision_cell_square]
    _ = HomologicalComplex.homologyMap (cellRelPairMap X r σ) q ≫ (cellPairIso X r q).hom := by
        rw [cellPairIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]

/-! ## Identification with the frozen `tgtDecomp` -/

/-- The `σ`-wise transport of the standard-cell excision isomorphism, as a map of the two
direct sums. -/
def mapRangeStd :
    ModuleCat.of (ZMod 2) (↑(X.nonDegenerate r) →₀
      ↥((relSingChainCx
        (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).homology q))
      ⟶ tgtSumMod X r q :=
  ModuleCat.ofHom (Finsupp.mapRange.linearMap (stdCellIso.{u} r q).hom.hom)

theorem bijective_stdCellIso_hom :
    Function.Bijective ((stdCellIso.{u} r q).hom.hom) :=
  (ConcreteCategory.isIso_iff_bijective ((stdCellIso.{u} r q).hom)).1 inferInstance

/-- The transported direct sum comparison is an isomorphism. -/
instance isIso_mapRangeStd : IsIso (mapRangeStd X r q) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hfun : ⇑(mapRangeStd X r q).hom
      = ⇑(Finsupp.mapRange.linearEquiv
        (LinearEquiv.ofBijective _ (bijective_stdCellIso_hom.{u} r q))) := rfl
  rw [hfun]
  exact (Finsupp.mapRange.linearEquiv
    (LinearEquiv.ofBijective _ (bijective_stdCellIso_hom.{u} r q))).bijective

/-- **The principal compatibility theorem.**  The singular cell-family decomposition
constructed above *is* the frozen comparison `tgtDecomp`. -/
theorem mapRangeStd_tgtDecomp :
    mapRangeStd X r q ≫ tgtDecomp X r q
      = sumCellHomology X r q ≫ (cellPairIso X r q).hom := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun σ m => ?_)
  show (tgtDecomp X r q).hom ((mapRangeStd X r q).hom (Finsupp.single σ m))
    = (cellPairIso X r q).hom.hom ((sumCellHomology X r q).hom (Finsupp.single σ m))
  have hmr : (mapRangeStd X r q).hom (Finsupp.single σ m)
      = Finsupp.single σ ((stdCellIso.{u} r q).hom.hom m) := by
    show Finsupp.mapRange _ (map_zero _) (Finsupp.single σ m) = _
    rw [Finsupp.mapRange_single]
  rw [hmr, tgtDecomp_single, sumCellHomology_single]
  exact congrFun (congrArg (fun g : (relSingChainCx
    (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).homology q ⟶
      (relChainCx (singSkInc X r)).homology q => ⇑g.hom)
    (cell_decomposition_square X r q σ)) m

/-! ## The frozen `tgtDecomp` is an isomorphism -/

/-- **The target decomposition.**  For an arbitrary family of attached `r`-cells the frozen
singular cell-family comparison is an isomorphism. -/
theorem isIso_tgtDecomp : IsIso (tgtDecomp X r q) := by
  haveI := isIso_sumCellHomology X r q
  have h : tgtDecomp X r q
      = inv (mapRangeStd X r q) ≫ sumCellHomology X r q ≫ (cellPairIso X r q).hom := by
    rw [← mapRangeStd_tgtDecomp, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [h]
  infer_instance

/-- The finite-family form of the target decomposition, retained for compatibility. -/
theorem isIso_tgtDecomp_finite [Fintype ↑(X.nonDegenerate r)] : IsIso (tgtDecomp X r q) :=
  isIso_tgtDecomp X r q

end Compare

end SpineTask24
