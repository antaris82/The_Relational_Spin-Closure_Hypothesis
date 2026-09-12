import RequestProject.Spine.Nerve.StandardCell.FundamentalClass

/-!
# Task 19, WP10 : the canonical relative class of the identity `r`-simplex

The top simplex of `Δ[r]` is the Yoneda identity `ULift.up (𝟙 ⦋r⦌)`.  Applying the unit of the
adjunction `SSet.toTop ⊣ TopCat.toSSet` turns it into a *characteristic singular `r`-simplex*
of `|Δ[r]|`.  This module proves that its singular boundary is carried by `|∂Δ[r]|`, so that it
defines a relative cycle, and packages the resulting class

`γ_r ∈ H_r^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)`.

* `SpineTask19.charSimp` — the characteristic singular `r`-simplex;
* `SpineTask19.bdFaceChain` — the sum of its codimension-one faces, as a chain on `|∂Δ[r]|`;
* `SpineTask19.charChain_boundary` — the singular boundary of the characteristic simplex is the
  image of that boundary chain (WP10.1);
* `SpineTask19.stdCellGenerator` — the relative class `γ_r` (WP10.2);
* `SpineTask19.stdCellGenerator_zero_ne_zero` — `γ_0 ≠ 0`, and `γ_0` is the canonical
  generator.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask14
  SpineTask18

universe u

namespace SpineTask19

/-! ## The characteristic singular simplex of the top simplex -/

/-- The top simplex of `Δ[r]`: the Yoneda identity. -/
def topSimp (r : ℕ) : (Δ[r] : SSet.{u}).obj (op (SimplexCategory.mk r)) := ULift.up (𝟙 _)

/-- **The characteristic singular `r`-simplex** of `|Δ[r]|`, obtained from the top simplex by
the unit of the realization/singular adjunction. -/
def charSimp (r : ℕ) : Sing (Cell.{u} r) r :=
  (sSetTopAdj.unit.app (Δ[r] : SSet.{u})).app (op (SimplexCategory.mk r)) (topSimp.{u} r)

/-- The corresponding singular `r`-chain. -/
def charChain (r : ℕ) : SSetChain (TopCat.toSSet.obj (Cell.{u} r)) r :=
  Finsupp.single (charSimp.{u} r) 1

/-! ## Its codimension-one faces live on the boundary -/

/-- The `i`-th face of the top simplex, as a simplex of `∂Δ[r]`. -/
def faceSimp (m : ℕ) (i : Fin (m + 2)) :
    ((∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex) : SSet.{u}).obj
      (op (SimplexCategory.mk m)) :=
  ⟨ULift.up (SimplexCategory.δ i), by
    show ¬ Function.Surjective (stdSimplex.asOrderHom
      (ULift.up (SimplexCategory.δ i) : (Δ[m + 1] : SSet.{u}).obj (op (SimplexCategory.mk m))))
    intro h
    obtain ⟨j, hj⟩ := h i
    exact (Fin.succAbove_ne i j) hj⟩

/-- The characteristic singular `(m)`-simplex of the `i`-th face, living on `|∂Δ[m+1]|`. -/
def bdFaceSimp (m : ℕ) (i : Fin (m + 2)) : Sing (Bd.{u} (m + 1)) m :=
  (sSetTopAdj.unit.app (((∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex)) : SSet.{u})).app
    (op (SimplexCategory.mk m)) (faceSimp.{u} m i)

/-- The sum of the codimension-one faces, as a chain on `|∂Δ[m+1]|`. -/
def bdFaceChain (m : ℕ) : SSetChain (TopCat.toSSet.obj (Bd.{u} (m + 1))) m :=
  ∑ i : Fin (m + 2), Finsupp.single (bdFaceSimp.{u} m i) 1

theorem stdCellPair_bdFaceSimp (m : ℕ) (i : Fin (m + 2)) :
    (stdCellPair.{u} (m + 1)).app (op (SimplexCategory.mk m)) (bdFaceSimp.{u} m i)
      = (TopCat.toSSet.obj (Cell.{u} (m + 1))).map (SimplexCategory.δ i).op
          (charSimp.{u} (m + 1)) := by
  have hnat0 := (sSetTopAdj.unit).naturality
    (((∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex)).ι)
  have hnat := congrFun (congrArg (fun φ => NatTrans.app φ (op (SimplexCategory.mk m))) hnat0)
    (faceSimp.{u} m i)
  have hnat2 := congrFun ((sSetTopAdj.unit.app (Δ[m + 1] : SSet.{u})).naturality
    (SimplexCategory.δ i).op) (topSimp.{u} (m + 1))
  refine Eq.trans hnat.symm (Eq.trans ?_ hnat2)
  rfl

/-- **WP10.1.**  The singular boundary of the characteristic top simplex is carried by the
realized boundary: it is the image of the sum of its codimension-one faces. -/
theorem charChain_boundary (m : ℕ) :
    sSetBoundary (TopCat.toSSet.obj (Cell.{u} (m + 1))) m (charChain.{u} (m + 1))
      = sSetChainMap (stdCellPair.{u} (m + 1)) m (bdFaceChain.{u} m) := by
  rw [bdFaceChain, map_sum]
  rw [sSetBoundary, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [charChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, sSetChainMap,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, stdCellPair_bdFaceSimp]
  rfl

/-! ## The relative class -/

/-- The characteristic chain, viewed in the relative complex. -/
def relCharChain (r : ℕ) : (relChainCx (stdCellPair.{u} r)).X r :=
  Submodule.Quotient.mk (charChain.{u} r)

/-- **WP10.2.**  The relative characteristic chain is a relative cycle. -/
theorem relCharChain_mem_Zc (r : ℕ) :
    relCharChain.{u} r ∈ Zc (relChainCx (stdCellPair.{u} r)) r := by
  rcases r with _ | m
  · exact mem_Zc_zero _
  · rw [mem_Zc_succ, relChainCx_d]
    show relBoundary (stdCellPair.{u} (m + 1)) m (Submodule.Quotient.mk (charChain.{u} (m + 1)))
      = 0
    rw [relBoundary_mk, charChain_boundary]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩

/-- **WP10.**  The canonical relative class `γ_r` of the identity `r`-simplex. -/
def stdCellGenerator (r : ℕ) : relHomology (stdCellPair.{u} r) r :=
  hcls (relCharChain.{u} r) (relCharChain_mem_Zc.{u} r)

/-! ## Degree zero -/

theorem pProj_hcls_charChain (r : ℕ) (h : charChain.{u} r ∈ Zc (singCx (Cell.{u} r)) r) :
    (pProj (stdCellPair.{u} r) r).hom (hcls (charChain.{u} r) h) = stdCellGenerator.{u} r := by
  rw [homologyMap_hcls]
  exact hcls_congr _ _ rfl

/-- **WP10, `r = 0`.**  The characteristic `0`-simplex gives a nonzero relative class. -/
theorem stdCellGenerator_zero_ne_zero : stdCellGenerator.{u} 0 ≠ 0 := by
  have hpt : hcls (K := singCx (Cell.{u} 0)) (charChain.{u} 0) (mem_Zc_zero _)
      = ptCls (Cell.{u} 0) (val0 (charSimp.{u} 0)) := by
    refine hcls_congr _ _ ?_
    show Finsupp.single (charSimp.{u} 0) 1
      = Finsupp.single (constSimp (val0 (charSimp.{u} 0)) 0) 1
    rw [← sing0_eq_const]
  haveI : Mono (pProj (stdCellPair.{u} 0) 0) :=
    (pair_exact₂ (stdCellPair.{u} 0) (stdCellPair_injective.{u} 0) 0).mono_g
      ((isZero_homology_of_isEmpty (X := Bd.{u} 0) 0).eq_zero_of_src _)
  have hinj : Function.Injective ((pProj (stdCellPair.{u} 0) 0).hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  intro hz
  refine ptCls_ne_zero (X := Cell.{u} 0) (val0 (charSimp.{u} 0)) ?_
  refine hinj ?_
  rw [map_zero, ← hpt] at *
  rw [pProj_hcls_charChain]
  exact hz

/-- **WP10, `r = 0`.**  `γ_0` is the canonical generator of the top relative homology. -/
theorem stdCellGenerator_zero_eq : stdCellGenerator.{u} 0 = stdCellTopClass.{u} 0 :=
  eq_lineGen_of_ne_zero _ stdCellGenerator_zero_ne_zero

end SpineTask19
