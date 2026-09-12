import RequestProject.Spine.Nerve.Comparison.Blockers
import RequestProject.Spine.AlgebraicTopology.RelativeChainCalculus
import RequestProject.Spine.Nerve.CellFamily.TargetMap
import RequestProject.Spine.Nerve.Comparison.SourceDecomposition

/-!
# Task 22, WP3/WP4 : the singular cell family, and componentwise compatibility of the frozen `J`

This module

* builds the **singular** cell-family comparison `tgtDecomp`, whose `σ`-component is the map of
  relative singular complexes induced by the realized characteristic map `|cellChar X r σ|`;
* proves the **componentwise compatibility of the frozen `relJ`**:

  ```
      ⊕_σ H_q^{simp}(Δ[r],∂Δ[r]) ──⊕_σ H_q(cellRelJ r)──▶ ⊕_σ H_q^{sing}(|Δ[r]|,|∂Δ[r]|)
              │                                                    │
       srcDecomp│                                                   │tgtDecomp
              ▼                                                    ▼
      H_q^{simp}(K^{(r)},K^{(r-1)}) ──H_q(relJ X r)──▶ H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|)
  ```

  commutes (`relJ_decomposition_square`), the bottom-left vertical being the **isomorphism**
  of `Task22FiniteCellAdditivity` and the top horizontal being exactly the Task-21 single-cell
  comparison `SpineTask20.cellRelJ r` on every component — no other map is chosen anywhere;
* records the generator-level form (`relJ_f_cellSimplex`, `relJ_generator_component`), derived
  from the frozen `SpineTask14.relJ_generator` and not reproved geometrically;
* states, as a `Prop` and **without assuming it anywhere**, the one statement Task 22 does not
  reach: that `tgtDecomp` is an isomorphism (`SingularCellFamilyAdditivity`), i.e. the finite
  singular cell-family decomposition.  See `TASK22_AUDIT.md`, WP3.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask13
  SpineTask14 SpineTask15 SpineTask19 SpineTask20 SpineTask21

universe u

namespace SpineTask22
/-! ## The componentwise compatibility of the frozen comparison

The composition calculus for `relChainCxMap` is generic and lives in
`RequestProject.Spine.AlgebraicTopology.RelativeChainCalculus`; the definitions
`topCellPairMap`, `tgtSumMod` and `tgtDecomp` live in
`RequestProject.Spine.Nerve.CellFamily.TargetMap`. -/

section Cells

variable (X : SSet.{u}) (r : ℕ)

/-- **The componentwise compatibility of the frozen comparison, at chain level.**

`cellPairMap σ ≫ relJ  =  cellRelJ r ≫ topCellPairMap σ`.

Both sides are the relative comparison attached to the unit-naturality square of the
characteristic map `cellChar X r σ`; nothing is chosen. -/
theorem cellPairMap_relJ (σ : X.nonDegenerate r) :
    cellPairMap X r σ ≫ relJ X r = cellRelJ.{u} r ≫ topCellPairMap X r σ := by
  rw [cellPairMap, relJ, relChainCxMap_comp, cellRelJ, topCellPairMap, relChainCxMap_comp]
  exact relChainCxMap_eq_of_v _ _ (sSetTopAdj.unit.naturality (cellChar X r σ))

end Cells

section Square

variable (X : SSet.{u}) (r q : ℕ)

/-- `⊕_σ H_q(cellRelJ r)` : the direct sum of the **Task-21 single-cell comparisons**, one on
each summand. -/
def sumCellRelJ : srcSumMod X r q ⟶ tgtSumMod X r q :=
  ModuleCat.ofHom (Finsupp.mapRange.linearMap
    (HomologicalComplex.homologyMap (cellRelJ.{u} r) q).hom)

theorem sumCellRelJ_single (σ : X.nonDegenerate r) (m : (simpRel.{u} r).homology q) :
    (sumCellRelJ X r q).hom (Finsupp.single σ m)
      = Finsupp.single σ ((HomologicalComplex.homologyMap (cellRelJ.{u} r) q).hom m) := by
  show Finsupp.mapRange (HomologicalComplex.homologyMap (cellRelJ.{u} r) q).hom (map_zero _)
    (Finsupp.single σ m) = _
  rw [Finsupp.mapRange_single]

theorem bijective_homologyMap_cellRelJ (r q : ℕ) :
    Function.Bijective ((HomologicalComplex.homologyMap (cellRelJ.{u} r) q).hom) := by
  haveI := isIso_homologyMap_cellRelJ.{u} r q
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- The Task-21 single-cell comparison as a linear equivalence. -/
def cellRelJEquiv (r q : ℕ) :
    ((simpRel.{u} r).homology q) ≃ₗ[ZMod 2] (relHomology (stdCellPair.{u} r) q) :=
  LinearEquiv.ofBijective _ (bijective_homologyMap_cellRelJ.{u} r q)

/-- The direct sum of the Task-21 single-cell comparisons is an isomorphism. -/
theorem isIso_sumCellRelJ : IsIso (sumCellRelJ X r q) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hfun : ⇑(sumCellRelJ X r q).hom
      = ⇑(Finsupp.mapRange.linearEquiv (cellRelJEquiv.{u} r q)) := rfl
  rw [hfun]
  exact (Finsupp.mapRange.linearEquiv (cellRelJEquiv.{u} r q)).bijective

/-- **The principal compatibility theorem of Task 22.**

The comparison square

```
⊕_σ H_q^{simp}(Δ[r],∂Δ[r]) ──⊕_σ H_q(cellRelJ r)──▶ ⊕_σ H_q^{sing}(|Δ[r]|,|∂Δ[r]|)
        │                                                    │
 srcDecomp│                                                   │tgtDecomp
        ▼                                                    ▼
H_q^{simp}(K^{(r)},K^{(r-1)}) ──H_q(relJ X r)──▶ H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|)
```

commutes.  The top horizontal map is the Task-21 single-cell comparison on every component,
and the left vertical map is the isomorphism `srcDecompIso`. -/
theorem relJ_decomposition_square :
    srcDecomp X r q ≫ HomologicalComplex.homologyMap (relJ X r) q
      = sumCellRelJ X r q ≫ tgtDecomp X r q := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun σ m => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  show (HomologicalComplex.homologyMap (relJ X r) q).hom
      ((srcDecomp X r q).hom (Finsupp.single σ m))
    = (tgtDecomp X r q).hom ((sumCellRelJ X r q).hom (Finsupp.single σ m))
  rw [srcDecomp_single, sumCellRelJ_single, tgtDecomp_single]
  have h1 : (HomologicalComplex.homologyMap (relJ X r) q).hom
      ((HomologicalComplex.homologyMap (cellPairMap X r σ) q).hom m)
      = (HomologicalComplex.homologyMap (cellPairMap X r σ ≫ relJ X r) q).hom m := by
    rw [HomologicalComplex.homologyMap_comp]; rfl
  have h2 : (HomologicalComplex.homologyMap (topCellPairMap X r σ) q).hom
      ((HomologicalComplex.homologyMap (cellRelJ.{u} r) q).hom m)
      = (HomologicalComplex.homologyMap (cellRelJ.{u} r ≫ topCellPairMap X r σ) q).hom m := by
    rw [HomologicalComplex.homologyMap_comp]; rfl
  rw [h1, h2, cellPairMap_relJ]

/-- **The same square in the form `H_q(relJ) = tgtDecomp ∘ (⊕_σ H_q(cellRelJ r)) ∘ srcDecomp⁻¹`.**
The source decomposition is an isomorphism (`isIso_srcDecomp`), so the frozen comparison is
*determined* by the Task-21 single-cell comparison together with `tgtDecomp`. -/
theorem homologyMap_relJ_eq :
    HomologicalComplex.homologyMap (relJ X r) q
      = (srcDecompIso X r q).inv ≫ sumCellRelJ X r q ≫ tgtDecomp X r q := by
  rw [← relJ_decomposition_square, ← Category.assoc]
  have : (srcDecompIso X r q).inv ≫ srcDecomp X r q = 𝟙 _ := (srcDecompIso X r q).inv_hom_id
  rw [this, Category.id_comp]

end Square

/-! ## Generator-level form -/

section Generators

variable (X : SSet.{u}) (r : ℕ)

/-- **The generator statement at chain level.**  The frozen comparison carries the relative
class of a nondegenerate `r`-simplex `σ` to the relative class of its **characteristic
singular simplex** `η(σ)`.  This is literally `SpineTask14.relJ_generator`. -/
theorem relJ_f_cellSimplex (σ : X.nonDegenerate r) :
    ((relJ X r).f r).hom
        (Submodule.Quotient.mk (Finsupp.single (cellSimplex σ) (1 : ZMod 2)))
      = Submodule.Quotient.mk
          (Finsupp.single (charSimplexSk X r (cellSimplex σ)) (1 : ZMod 2)) :=
  relJ_generator X r _ 1

/-- **The generator statement at homology level.**  `e_σ ↦ γ_σ`. -/
theorem relJ_topCls (σ : X.nonDegenerate r) :
    (HomologicalComplex.homologyMap (relJ X r) r).hom
        (topCls X r (Finsupp.single (cellSimplex σ) (1 : ZMod 2)))
      = hcls (K := relChainCx (singSkInc X r))
          (Submodule.Quotient.mk
            (Finsupp.single (charSimplexSk X r (cellSimplex σ)) (1 : ZMod 2)))
          (relJ_f_cellSimplex X r σ ▸ map_mem_Zc r (relJ X r) (mem_Zc_top X r _)) := by
  rw [topCls_apply, homologyMap_hcls]
  exact hcls_congr _ _ (relJ_f_cellSimplex X r σ)

/-- **The generator statement under the finite-family decompositions.**  The `σ`-summand of the
simplicial standard-cell generator `e_r` is carried to the `σ`-summand of the singular
standard-cell generator `stdCellGenerator r`. -/
theorem relJ_generator_component (σ : X.nonDegenerate r) :
    (HomologicalComplex.homologyMap (relJ X r) r).hom
        ((srcDecomp X r r).hom (Finsupp.single σ (simpTopClass.{u} r)))
      = (tgtDecomp X r r).hom (Finsupp.single σ (stdCellGenerator.{u} r)) := by
  have hsq := congrArg (fun (g : srcSumMod X r r ⟶ (relChainCx (singSkInc X r)).homology r) =>
    g.hom (Finsupp.single σ (simpTopClass.{u} r))) (relJ_decomposition_square X r r)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  rw [hsq, sumCellRelJ_single, homologyMap_cellRelJ_simpTopClass]

end Generators

/-! ## WP3 : the singular finite-family decomposition — the remaining statement

The following is **not** proved and **not** assumed anywhere in this project.  It is stated as
a `Prop` so that the exact remaining gap is visible in Lean, in the same style as the Task-14
blockers `SpineTask14.RelJIsIso`, `SpineTask14.StandardCellPairAcyclic`.
-/

/-- **The finite singular cell-family decomposition (open).**  For a *finite* family of
attached `r`-cells, the realized characteristic maps should induce

`⊕_{σ ∈ X.nonDegenerate r} H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂) ≅ H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|;ℤ₂)`.

Classically this follows from the Task-15 realized pushout together with Task-18 excision,
applied to an open neighbourhood of the union of the open cells that deformation retracts onto
it.  The pinned environment has the pushout and excision but not the point-set separation
statement; see `TASK22_AUDIT.md`. -/
def SingularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ) : Prop :=
  ∀ q, IsIso (tgtDecomp X r q)

/-- **The conditional finite-cell-family `RelJIsIso`.**  *Finite-cell-family only* — and in
fact conditional on the still open `SingularCellFamilyAdditivity`.  It is recorded here only to
make explicit that the sole remaining input to blocker B3 for one skeletal step is the
singular cell-family decomposition: the source decomposition and the componentwise
compatibility of the frozen `relJ` are proved unconditionally above. -/
theorem relJIsIso_of_singularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ)
    (h : SingularCellFamilyAdditivity X r) : SpineTask14.RelJIsIso X r := by
  intro q
  haveI := isIso_srcDecomp X r q
  haveI := isIso_sumCellRelJ X r q
  haveI := h q
  rw [homologyMap_relJ_eq X r q]
  infer_instance

end SpineTask22
