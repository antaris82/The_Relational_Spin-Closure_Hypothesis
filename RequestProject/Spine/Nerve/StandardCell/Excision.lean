import RequestProject.Spine.Nerve.CellFamily.ExcisionCompatibility
import RequestProject.Spine.Nerve.Geometry.OpenStandardCell
import RequestProject.Spine.Nerve.StandardCell.Pair

/-!
# Task 23 — the single standard cell: excising the boundary

This module carries out, for the *standard* cell alone, the two steps that Task 23 WP5 carried
out for the attached family:

* `bdryHomotopyEquiv` — the punctured cell `|Δ[r]| \ {b_r}` deformation retracts onto
  `|∂Δ[r]|`, so the inclusion is a homotopy equivalence (Task 23 WP2);
* `isIso_homologyMap_stdPair` — hence
  `H_q^{sing}(|Δ[r]|, |∂Δ[r]|) ≅ H_q^{sing}(|Δ[r]|, |Δ[r]| \ {b_r})`;
* `stdExcisionIso` — Task-18 excision at the excisive pair
  `(|Δ[r]| \ |∂Δ[r]|, |Δ[r]| \ {b_r})`, giving
  `H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(|Δ[r]|, |Δ[r]| \ {b_r})`;
* `stdCellIso` — the composite
  `H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(|Δ[r]|, |∂Δ[r]|)`.

This is the local (single-cell) half of the finite cell-family decomposition.
-/

noncomputable section

open CategoryTheory Limits Simplicial SSet NerveGeom SpineTask13 SpineTask14 SpineTask15
  SpineTask17 SpineTask18 SpineTask19

universe u

namespace SpineTask23

section StandardCell

variable (r : ℕ)

/-- The realized boundary, as a map into the punctured cell, as a morphism of `TopCat`. -/
def bdryToPuncturedMap :
    SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶
      SpineTask18.subTop (puncturedCell.{u} r) :=
  TopCat.ofHom (bdryToPunctured.{u} r)

/-- The homotopy `id ≃ bdryToPunctured ∘ cellRetract` of the punctured cell. -/
def cellHomotopyStruct : (ContinuousMap.id ↥(puncturedCell.{u} r)).Homotopy
    ((bdryToPunctured.{u} r).comp (cellRetract.{u} r)) where
  toFun := cellHomotopy.{u} r
  continuous_toFun := (cellHomotopy.{u} r).continuous
  map_zero_left := cellHomotopy_zero.{u} r
  map_one_left := fun x => Subtype.ext (cellHomotopy_one.{u} r x)

/-- **The inclusion `|∂Δ[r]| ↪ |Δ[r]| \ {b_r}` is a homotopy equivalence.** -/
def bdryHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))
      ↥(puncturedCell.{u} r) where
  toFun := bdryToPunctured.{u} r
  invFun := cellRetract.{u} r
  left_inv := by
    have h : (cellRetract.{u} r).comp (bdryToPunctured.{u} r) = ContinuousMap.id _ :=
      ContinuousMap.ext (cellRetract_bdryToPunctured.{u} r)
    rw [h]
  right_inv := ⟨(cellHomotopyStruct.{u} r).symm⟩

theorem isIso_homologyMap_bdryToPunctured (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (TopCat.toSSet.map (bdryToPuncturedMap.{u} r))) q) := by
  have h := isIso_homologyMap_of_homotopyEquiv
    (X := SSet.toTop.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))
    (Y := TopCat.of ↥(puncturedCell.{u} r)) (bdryHomotopyEquiv.{u} r) q
  exact h

theorem bdryToPuncturedMap_subInc :
    bdryToPuncturedMap.{u} r ≫ SpineTask18.subInc (puncturedCell.{u} r)
      = SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι := by
  refine ConcreteCategory.hom_ext _ _ fun b => ?_
  rfl

theorem square_stdPair :
    stdCellPair.{u} r ≫ 𝟙 _
      = TopCat.toSSet.map (bdryToPuncturedMap.{u} r)
        ≫ TopCat.toSSet.map (SpineTask18.subInc (puncturedCell.{u} r)) := by
  rw [Category.comp_id, ← TopCat.toSSet.map_comp, bdryToPuncturedMap_subInc]

/-- **The comparison of pairs `(|Δ[r]|, |∂Δ[r]|) ⟶ (|Δ[r]|, |Δ[r]| \ {b_r})`.** -/
def stdPairMap : relChainCx (stdCellPair.{u} r)
    ⟶ relChainCx (TopCat.toSSet.map (SpineTask18.subInc (puncturedCell.{u} r))) :=
  relChainCxMap (stdCellPair.{u} r)
    (TopCat.toSSet.map (SpineTask18.subInc (puncturedCell.{u} r)))
    (TopCat.toSSet.map (bdryToPuncturedMap.{u} r)) (𝟙 _) (square_stdPair.{u} r)

/-- **`H_q^{sing}(|Δ[r]|, |∂Δ[r]|) ≅ H_q^{sing}(|Δ[r]|, |Δ[r]| \ {b_r})`.** -/
theorem isIso_homologyMap_stdPair (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (stdPairMap.{u} r) q) :=
  isIso_homologyMap_relChainCxMap _ _ _ _ (square_stdPair.{u} r)
    (toSSet_map_injective _ (SpineTask16.standardCellMono.{u} r))
    (toSSet_map_injective _ (SpineTask18.subInc_injective _))
    (isIso_homologyMap_bdryToPunctured.{u} r) (isIso_homologyMap_id _) q

def stdPairIso (q : ℕ) :
    (relChainCx (stdCellPair.{u} r)).homology q
      ≅ (relChainCx (TopCat.toSSet.map (SpineTask18.subInc (puncturedCell.{u} r)))).homology q :=
  haveI := isIso_homologyMap_stdPair.{u} r q
  asIso (HomologicalComplex.homologyMap (stdPairMap.{u} r) q)

/-! ## Excising the boundary of the standard cell -/

/-! The open cell `Δ°` itself, and its elementary point-set properties, are in
`RequestProject.Spine.Nerve.Geometry.OpenStandardCell`. -/

/-- **Excision on the standard cell.**
`H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(|Δ[r]|, |Δ[r]| \ {b_r})`. -/
def stdExcisionIso (q : ℕ) :
    (relSingChainCx
      (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).homology q
      ≅ (relSingChainCx (SpineTask18.subInc (puncturedCell.{u} r))).homology q :=
  SpineTask18.excisionIso (openStdCell.{u} r) (puncturedCell.{u} r) (isOpen_openStdCell.{u} r)
    (isOpen_puncturedCell.{u} r) (openStdCell_union_puncturedCell.{u} r) q

/-- **The single-cell comparison.**
`H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(|Δ[r]|, |∂Δ[r]|)`. -/
def stdCellIso (q : ℕ) :
    (relSingChainCx
      (SpineTask18.incInterU (openStdCell.{u} r) (puncturedCell.{u} r))).homology q
      ≅ (relChainCx (stdCellPair.{u} r)).homology q :=
  (stdExcisionIso.{u} r q).trans (stdPairIso.{u} r q).symm

end StandardCell

end SpineTask23
