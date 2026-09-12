import RequestProject.Spine.Nerve.StandardCell.BoundaryTwoSetCover

/-!
# Task 20 : the canonical standard-cell generator

Task 19 constructed two objects in the top relative homology of the standard cell pair:

* `SpineTask19.stdCellTopClass r` — the unique nonzero element of the one-dimensional
  `H_r(|Δ[r]|,|∂Δ[r]|;ℤ₂)`;
* `SpineTask19.stdCellGenerator r` — the class `γ_r` of the *identity `r`-simplex*.

They agree for `r = 0`.  This module proves that they agree for every `r`.  The only missing
point was the nonvanishing of the class of the face sum

`bdFaceChain m ∈ C_m(|∂Δ[m+1]|)`

which is what the connecting map sends `γ_{m+1}` to.  That is proved here by induction on `m`,
by the following elementary argument (no new Mayer–Vietoris machinery, no horn homology):

* `|∂Δ[m+2]|` is covered by the two open sets `Uset`, `Vset` of `Task20Cover`;
* the face sum splits as a chain carried by `Uset` plus the `0`-th face, carried by `Vset`;
* the boundary of the `Uset`-part is exactly the image of the face sum one dimension down,
  under the `0`-th face map `|∂Δ[m+1]| → Uset ∩ Vset`, which admits a **retraction**
  (`SpineTask20.retr`), so it is injective on homology;
* hence the relative class of the `Uset`-part in `H(Uset, Uset ∩ Vset)` is nonzero, and by the
  Task-18 excision theorem so is the class of the face sum in `H(|∂Δ[m+2]|, Vset)`, hence in
  `H_{m+1}(|∂Δ[m+2]|)`.

The base case `m = 0` is the pair of distinct points of `|∂Δ[1]|`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask14
  SpineTask18 SpineTask19

universe u

namespace SpineTask20

/-! ## Splitting the face sum along the cover -/

variable (n : ℕ)

/-- In characteristic two, adding the same element twice changes nothing. -/
theorem add_add_self_cancel {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (a b : M) :
    a + b + b = a := by rw [add_assoc, mod2_add_self, add_zero]

theorem bdFaceChain_add_single_zero :
    bdFaceChain.{u} (n + 1) + Finsupp.single (bdFaceSimp.{u} (n + 1) 0) 1
      = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 3)),
          Finsupp.single (bdFaceSimp.{u} (n + 1) i) 1 := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 3)))
    (fun i => Finsupp.single (bdFaceSimp.{u} (n + 1) i) (1 : ZMod 2)) (Finset.mem_univ 0)
  exact (congrArg (fun x => x + Finsupp.single (bdFaceSimp.{u} (n + 1) 0) (1 : ZMod 2))
    h.symm).trans (add_add_self_cancel _ _)

theorem exists_chainU :
    ∃ zU : SSetChain (TopCat.toSSet.obj (subTop (Uset.{u} n))) (n + 1),
      sSetChainMap (TopCat.toSSet.map (subInc (Uset.{u} n))) (n + 1) zU
        = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 3)),
            Finsupp.single (bdFaceSimp.{u} (n + 1) i) 1 := by
  have hmem : (∑ i ∈ Finset.univ.erase (0 : Fin (n + 3)),
        Finsupp.single (bdFaceSimp.{u} (n + 1) i) (1 : ZMod 2))
      ∈ LinearMap.range (sSetChainMap (TopCat.toSSet.map (subInc (Uset.{u} n))) (n + 1)) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨τ, hτ⟩ : bdFaceSimp.{u} (n + 1) i ∈ Set.range
        ((TopCat.toSSet.map (subInc (Uset.{u} n))).app (op (SimplexCategory.mk (n + 1)))) := by
      rw [range_toSSet_subInc]
      exact carrier_bdFaceSimp_subset_Uset n i (Finset.ne_of_mem_erase hi)
    exact ⟨Finsupp.single τ 1, by rw [sSetChainMap_single, hτ]⟩
  exact hmem

theorem exists_chainV :
    ∃ zV : SSetChain (TopCat.toSSet.obj (subTop (Vset.{u} n))) (n + 1),
      sSetChainMap (TopCat.toSSet.map (subInc (Vset.{u} n))) (n + 1) zV
        = Finsupp.single (bdFaceSimp.{u} (n + 1) 0) 1 := by
  obtain ⟨τ, hτ⟩ : bdFaceSimp.{u} (n + 1) 0 ∈ Set.range
      ((TopCat.toSSet.map (subInc (Vset.{u} n))).app (op (SimplexCategory.mk (n + 1)))) := by
    rw [range_toSSet_subInc]
    exact carrier_bdFaceSimp_subset_Vset n
  exact ⟨Finsupp.single τ 1, by rw [sSetChainMap_single, hτ]⟩

/-- The face sum of `|∂Δ[n+1]|`, pushed into the intersection of the cover. -/
def interChain : SSetChain (TopCat.toSSet.obj (subTop (Uset.{u} n ∩ Vset.{u} n))) n :=
  sSetChainMap (TopCat.toSSet.map (gIn.{u} n)) n (bdFaceChain.{u} n)

/-- The face sum is a cycle, in the form used below. -/
theorem sSetBoundary_bdFaceChain (m : ℕ) :
    sSetBoundary (TopCat.toSSet.obj (Bd.{u} (m + 2))) m (bdFaceChain.{u} (m + 1)) = 0 := by
  have h := bdFaceChain_mem_Zc.{u} (m + 1)
  rw [mem_Zc_succ, show ((singCx (Bd.{u} (m + 2))).d (m + 1) m).hom
      = sSetBoundary (TopCat.toSSet.obj (Bd.{u} (m + 2))) m from
    sSetChainComplexFunctor_d (TopCat.toSSet.obj (Bd.{u} (m + 2))) m] at h
  exact h

/-- The boundary of the `Uset`-part of the face sum is carried by the intersection, where it is
the face sum one dimension down. -/
theorem incInterU_interChain (zU : SSetChain (TopCat.toSSet.obj (subTop (Uset.{u} n))) (n + 1))
    (hzU : sSetChainMap (TopCat.toSSet.map (subInc (Uset.{u} n))) (n + 1) zU
      = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 3)),
          Finsupp.single (bdFaceSimp.{u} (n + 1) i) 1) :
    sSetChainMap (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n (interChain.{u} n)
      = sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n))) n zU := by
  refine sSetChainMap_injective (TopCat.toSSet.map (subInc (Uset.{u} n))) n
    (toSSet_map_injective _ (subInc_injective _) _) ?_
  have hL : sSetChainMap (TopCat.toSSet.map (subInc (Uset.{u} n))) n
        (sSetChainMap (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n
          (interChain.{u} n))
      = sSetChainMap (TopCat.toSSet.map (bdFaceTop.{u} (n + 1))) n (bdFaceChain.{u} n) := by
    rw [interChain, sSetChainMap_comp, sSetChainMap_comp, ← TopCat.toSSet.map_comp,
      ← TopCat.toSSet.map_comp]
    rfl
  have hR := congrFun (congrArg DFunLike.coe
    (sSetBoundary_naturality (TopCat.toSSet.map (subInc (Uset.{u} n))) n)) zU
  simp only [LinearMap.comp_apply] at hR
  rw [hL, hR, hzU, ← bdFaceChain_add_single_zero, map_add, sSetBoundary_bdFaceChain, zero_add,
    boundary_single_bdFaceSimp_zero]

/-- The class of the face sum of `|∂Δ[n+1]|` inside the intersection of the cover is nonzero,
because the `0`-th face map admits a retraction. -/
theorem interChain_mem_Zc :
    interChain.{u} n ∈ Zc (singCx (subTop (Uset.{u} n ∩ Vset.{u} n))) n :=
  map_mem_Zc n (singCxMap (gIn.{u} n)) (bdFaceChain_mem_Zc n)

theorem homologyMap_retr_gIn (x : (singCx (Bd.{u} (n + 1))).homology n) :
    (HomologicalComplex.homologyMap (singCxMap (retr.{u} n)) n).hom
      ((HomologicalComplex.homologyMap (singCxMap (gIn.{u} n)) n).hom x) = x := by
  have hfun : singCxMap (gIn.{u} n) ≫ singCxMap (retr.{u} n) = 𝟙 (singCx (Bd.{u} (n + 1))) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, gIn_comp_retr,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have h := congrArg (fun f : (singCx (Bd.{u} (n + 1))) ⟶ (singCx (Bd.{u} (n + 1))) =>
      (HomologicalComplex.homologyMap f n).hom x) hfun
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at h
  exact h

theorem hcls_interChain_ne_zero
    (ih : hcls (K := singCx (Bd.{u} (n + 1))) (bdFaceChain.{u} n) (bdFaceChain_mem_Zc n) ≠ 0) :
    hcls (K := singCx (subTop (Uset.{u} n ∩ Vset.{u} n))) (interChain.{u} n)
      (interChain_mem_Zc.{u} n) ≠ 0 := by
  intro h0
  refine ih ?_
  have h1 : (HomologicalComplex.homologyMap (singCxMap (gIn.{u} n)) n).hom
      (hcls (K := singCx (Bd.{u} (n + 1))) (bdFaceChain.{u} n) (bdFaceChain_mem_Zc n))
      = hcls (K := singCx (subTop (Uset.{u} n ∩ Vset.{u} n))) (interChain.{u} n)
          (interChain_mem_Zc.{u} n) := by
    rw [homologyMap_hcls]
    exact hcls_congr _ _ rfl
  have h2 := congrArg (HomologicalComplex.homologyMap (singCxMap (retr.{u} n)) n).hom h1
  rw [homologyMap_retr_gIn, h0, map_zero] at h2
  exact h2

/-! ## The inductive step -/

/-- **The inductive step.**  If the face sum of `|∂Δ[n+1]|` is not a boundary, neither is the
face sum of `|∂Δ[n+2]|`. -/
theorem hcls_bdFaceChain_step
    (ih : hcls (K := singCx (Bd.{u} (n + 1))) (bdFaceChain.{u} n) (bdFaceChain_mem_Zc n) ≠ 0) :
    hcls (K := singCx (Bd.{u} (n + 2))) (bdFaceChain.{u} (n + 1))
      (bdFaceChain_mem_Zc (n + 1)) ≠ 0 := by
  intro hz
  obtain ⟨zU, hzU⟩ := exists_chainU.{u} n
  obtain ⟨zV, hzV⟩ := exists_chainV.{u} n
  -- `zU` is a relative cycle of the pair `(Uset, Uset ∩ Vset)`
  have hrelcyc : (Submodule.Quotient.mk zU :
        RelChainMod (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) (n + 1))
      ∈ Zc (relSingChainCx (incInterU (Uset.{u} n) (Vset.{u} n))) (n + 1) := by
    rw [mem_Zc_succ, relChainCx_d]
    show relBoundary _ n (Submodule.Quotient.mk zU) = 0
    rw [relBoundary_mk]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨interChain.{u} n, incInterU_interChain n zU hzU⟩
  -- its relative class is nonzero
  have ha : hcls (K := relSingChainCx (incInterU (Uset.{u} n) (Vset.{u} n)))
      (Submodule.Quotient.mk zU) hrelcyc ≠ 0 := by
    intro h0
    rw [hcls_eq_zero_iff] at h0
    obtain ⟨W, hW⟩ := h0
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ W
    rw [relChainCx_d] at hW
    have hW' : (Submodule.Quotient.mk
          (sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n))) (n + 1) t) :
        RelChainMod (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) (n + 1))
        = Submodule.Quotient.mk zU := hW
    obtain ⟨s, hs⟩ := (Submodule.Quotient.eq _).1 hW'
    have hzUeq : zU = sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n))) (n + 1) t
        - sSetChainMap (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) (n + 1) s := by
      rw [hs]; abel
    have hdd := congrFun (congrArg DFunLike.coe
      (SpineTask13.sSetBoundary_comp_sSetBoundary
        (TopCat.toSSet.obj (subTop (Uset.{u} n))) n)) t
    have hnat := congrFun (congrArg DFunLike.coe
      (sSetBoundary_naturality (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n)) s
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd hnat
    have hbd : sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n))) n zU
        = - sSetChainMap (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n
            (sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n ∩ Vset.{u} n))) n s) := by
      rw [hzUeq, map_sub, hdd, hnat]
      abel
    have heq : sSetChainMap (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n
          (interChain.{u} n)
        = sSetChainMap (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n
            (- sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n ∩ Vset.{u} n))) n s) := by
      rw [incInterU_interChain n zU hzU, hbd, map_neg]
    have hfinal := sSetChainMap_injective
      (TopCat.toSSet.map (incInterU (Uset.{u} n) (Vset.{u} n))) n
      (toSSet_map_injective _ (incInterU_injective _ _) _) heq
    refine hcls_interChain_ne_zero n ih ?_
    rw [hcls_eq_zero_iff]
    refine ⟨-s, ?_⟩
    rw [show ((singCx (subTop (Uset.{u} n ∩ Vset.{u} n))).d (n + 1) n).hom
        = sSetBoundary (TopCat.toSSet.obj (subTop (Uset.{u} n ∩ Vset.{u} n))) n from
      sSetChainComplexFunctor_d _ n, map_neg]
    exact hfinal.symm
  -- excision transports it to the pair `(|∂Δ[n+2]|, Vset)`
  haveI : IsIso (HomologicalComplex.homologyMap (excisionMap (Uset.{u} n) (Vset.{u} n)) (n + 1)) :=
    isIso_homologyMap_excisionMap (Uset.{u} n) (Vset.{u} n) (isOpen_Uset n) (isOpen_Vset n)
      (Uset_union_Vset n) (n + 1)
  have hinj : Function.Injective
      ((HomologicalComplex.homologyMap (excisionMap (Uset.{u} n) (Vset.{u} n)) (n + 1)).hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine ha (hinj ?_)
  rw [map_zero, homologyMap_hcls]
  obtain ⟨t, ht⟩ := (hcls_eq_zero_iff _ (bdFaceChain_mem_Zc (n + 1))).1 hz
  rw [show ((singCx (Bd.{u} (n + 2))).d (n + 2) (n + 1)).hom
      = sSetBoundary (TopCat.toSSet.obj (Bd.{u} (n + 2))) (n + 1) from
    sSetChainComplexFunctor_d _ (n + 1)] at ht
  have hquot : ((excisionMap (Uset.{u} n) (Vset.{u} n)).f (n + 1)).hom
        (Submodule.Quotient.mk zU)
      = (Submodule.Quotient.mk (bdFaceChain.{u} (n + 1)) :
          RelChainMod (TopCat.toSSet.map (subInc (Vset.{u} n))) (n + 1)) := by
    show (Submodule.Quotient.mk
        (sSetChainMap (TopCat.toSSet.map (subInc (Uset.{u} n))) (n + 1) zU)
      : RelChainMod (TopCat.toSSet.map (subInc (Vset.{u} n))) (n + 1)) = _
    rw [hzU, ← bdFaceChain_add_single_zero, Submodule.Quotient.mk_add,
      show (Submodule.Quotient.mk (Finsupp.single (bdFaceSimp.{u} (n + 1) 0) 1)
        : RelChainMod (TopCat.toSSet.map (subInc (Vset.{u} n))) (n + 1)) = 0 from
      (Submodule.Quotient.mk_eq_zero _).2 ⟨zV, hzV⟩, add_zero]
  rw [hcls_congr _ (map_mem_Zc (n + 1) (relProj (TopCat.toSSet.map (subInc (Vset.{u} n))))
    (bdFaceChain_mem_Zc (n + 1))) hquot, hcls_eq_zero_iff]
  refine ⟨Submodule.Quotient.mk t, ?_⟩
  rw [relChainCx_d]
  show (Submodule.Quotient.mk
      (sSetBoundary (TopCat.toSSet.obj (Bd.{u} (n + 2))) (n + 1) t)
    : RelChainMod (TopCat.toSSet.map (subInc (Vset.{u} n))) (n + 1)) = _
  exact congrArg (Submodule.Quotient.mk
    (p := LinearMap.range (sSetChainMap (TopCat.toSSet.map (subInc (Vset.{u} n))) (n + 1)))) ht

/-! ## The base case -/

/-- **The base case.**  The two vertices of `|∂Δ[1]|` are distinct, so their sum is the
distinguished class `β₁`. -/
theorem hcls_bdFaceChain_zero :
    hcls (K := singCx (Bd.{u} 1)) (bdFaceChain.{u} 0) (bdFaceChain_mem_Zc 0)
      = bdFundClass.{u} 1 := by
  have hpt : ∀ i : Fin 2, hcls (K := singCx (Bd.{u} 1))
      (Finsupp.single (bdFaceSimp.{u} 0 i) 1) (mem_Zc_zero _)
      = ptCls (Bd.{u} 1) (val0 (bdFaceSimp.{u} 0 i)) := by
    intro i
    refine hcls_congr _ _ ?_
    show Finsupp.single (bdFaceSimp.{u} 0 i) 1
      = Finsupp.single (constSimp (val0 (bdFaceSimp.{u} 0 i)) 0) 1
    rw [← sing0_eq_const]
  have hne : val0 (bdFaceSimp.{u} 0 0) ≠ val0 (bdFaceSimp.{u} 0 1) := by
    have h0 : (SpineTask16.bdCoord.{u} 1 (val0 (bdFaceSimp.{u} 0 0)) : Fin 2 → ℝ) 0 = 0 :=
      bdCoord_carrier_bdFaceSimp 0 0 ⟨pt0, rfl⟩
    have h1 : (SpineTask16.bdCoord.{u} 1 (val0 (bdFaceSimp.{u} 0 1)) : Fin 2 → ℝ) 1 = 0 :=
      bdCoord_carrier_bdFaceSimp 0 1 ⟨pt0, rfl⟩
    intro heq
    rw [heq] at h0
    have hsum1 := stdSimplex.sum_eq_one (SpineTask16.bdCoord.{u} 1 (val0 (bdFaceSimp.{u} 0 1)))
    rw [Fin.sum_univ_two, h0, h1, add_zero] at hsum1
    exact zero_ne_one hsum1
  have hcl : hcls (K := singCx (Bd.{u} 1)) (bdFaceChain.{u} 0) (bdFaceChain_mem_Zc 0)
      = ptCls (Bd.{u} 1) (val0 (bdFaceSimp.{u} 0 0))
        + ptCls (Bd.{u} 1) (val0 (bdFaceSimp.{u} 0 1)) := by
    rw [← hpt 0, ← hpt 1, ← hcls_add]
    refine hcls_congr _ _ ?_
    exact Fin.sum_univ_two (fun i => Finsupp.single (bdFaceSimp.{u} 0 i) (1 : ZMod 2))
  rw [hcl]
  show _ = ptCls (Bd.{u} 1) (bdOnePt.{u} 0) + ptCls (Bd.{u} 1) (bdOnePt.{u} 1)
  rcases bdOnePt_all.{u} (val0 (bdFaceSimp.{u} 0 0)) with hv0 | hv0 <;>
    rcases bdOnePt_all.{u} (val0 (bdFaceSimp.{u} 0 1)) with hv1 | hv1
  · exact absurd (hv0.trans hv1.symm) hne
  · rw [hv0, hv1]
  · rw [hv0, hv1]; exact add_comm _ _
  · exact absurd (hv0.trans hv1.symm) hne

/-! ## The face-sum class -/

/-- **The face-sum cycle is not a boundary**, in every dimension. -/
theorem hcls_bdFaceChain_ne_zero : ∀ (m : ℕ),
    hcls (K := singCx (Bd.{u} (m + 1))) (bdFaceChain.{u} m) (bdFaceChain_mem_Zc m) ≠ 0
  | 0 => by
      rw [hcls_bdFaceChain_zero.{u}]
      exact bdFundClass_ne_zero.{u} 1 (by omega)
  | (m + 1) => hcls_bdFaceChain_step.{u} m (hcls_bdFaceChain_ne_zero m)

/-- **The missing Task-19 compatibility.**  The class of the sum of the codimension-one faces
of the identity `(m+1)`-simplex *is* the distinguished mod-2 fundamental class of
`|∂Δ[m+1]|`. -/
theorem hcls_bdFaceChain_eq_bdFundClass (m : ℕ) :
    hcls (K := singCx (Bd.{u} (m + 1))) (bdFaceChain.{u} m) (bdFaceChain_mem_Zc m)
      = bdFundClass.{u} (m + 1) := by
  match m with
  | 0 => exact hcls_bdFaceChain_zero.{u}
  | (k + 1) =>
      rw [bdFundClass_eq_lineGen.{u} k]
      exact eq_lineGen_of_ne_zero _ (hcls_bdFaceChain_ne_zero.{u} (k + 1))

/-! ## The canonical generator -/

/-- **The principal theorem, nonvanishing.**  The relative class of the identity `r`-simplex is
nonzero for every `r`. -/
theorem stdCellGenerator_ne_zero : ∀ (r : ℕ), stdCellGenerator.{u} r ≠ 0
  | 0 => stdCellGenerator_zero_ne_zero.{u}
  | (m + 1) => by
      intro h0
      rw [stdCellGenerator, hcls_eq_zero_iff] at h0
      obtain ⟨W, hW⟩ := h0
      obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ W
      rw [relChainCx_d] at hW
      have hW' : (Submodule.Quotient.mk
            (sSetBoundary (TopCat.toSSet.obj (Cell.{u} (m + 1))) (m + 1) t) :
          RelChainMod (stdCellPair.{u} (m + 1)) (m + 1))
          = Submodule.Quotient.mk (charChain.{u} (m + 1)) := hW
      obtain ⟨s, hs⟩ := (Submodule.Quotient.eq _).1 hW'
      have hcc : charChain.{u} (m + 1)
          = sSetBoundary (TopCat.toSSet.obj (Cell.{u} (m + 1))) (m + 1) t
            - sSetChainMap (stdCellPair.{u} (m + 1)) (m + 1) s := by
        rw [hs]; abel
      have hdd := congrFun (congrArg DFunLike.coe
        (SpineTask13.sSetBoundary_comp_sSetBoundary
          (TopCat.toSSet.obj (Cell.{u} (m + 1))) m)) t
      have hnat := congrFun (congrArg DFunLike.coe
        (sSetBoundary_naturality (stdCellPair.{u} (m + 1)) m)) s
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd hnat
      have hbd : sSetChainMap (stdCellPair.{u} (m + 1)) m (bdFaceChain.{u} m)
          = sSetChainMap (stdCellPair.{u} (m + 1)) m
              (- sSetBoundary (TopCat.toSSet.obj (Bd.{u} (m + 1))) m s) := by
        rw [map_neg, ← charChain_boundary.{u} m, hcc, map_sub, hdd, hnat]
        abel
      have hfinal := sSetChainMap_injective (stdCellPair.{u} (m + 1)) m
        (stdCellPair_injective.{u} (m + 1) _) hbd
      refine hcls_bdFaceChain_ne_zero.{u} m ?_
      rw [hcls_eq_zero_iff]
      refine ⟨-s, ?_⟩
      rw [show ((singCx (Bd.{u} (m + 1))).d (m + 1) m).hom
          = sSetBoundary (TopCat.toSSet.obj (Bd.{u} (m + 1))) m from
        sSetChainComplexFunctor_d _ m, map_neg]
      exact hfinal.symm

/-- **The principal theorem.**  The relative class of the identity `r`-simplex *is* the
canonical generator of the top relative homology of the standard cell pair. -/
theorem stdCellGenerator_eq_stdCellTopClass (r : ℕ) :
    stdCellGenerator.{u} r = stdCellTopClass.{u} r :=
  eq_lineGen_of_ne_zero _ (stdCellGenerator_ne_zero.{u} r)

/-- **The connecting-map compatibility.**  For `r > 0` the connecting homomorphism of the pair
sends the characteristic relative class to the distinguished boundary class. -/
theorem pairDelta_stdCellGenerator (k : ℕ) :
    (pairDelta (stdCellPair.{u} (k + 1)) (stdCellPair_injective.{u} (k + 1)) k).hom
        (stdCellGenerator.{u} (k + 1))
      = bdFundClass.{u} (k + 1) := by
  rw [stdCellGenerator_eq_stdCellTopClass.{u} (k + 1)]
  match k with
  | 0 => exact pairDelta_stdCellTopClass_one.{u}
  | (j + 1) => exact pairDelta_stdCellTopClass_succ.{u} j


/-! ## The single-cell comparison map (optional corollary) -/

/-- The comparison of relative chain complexes for the standard cell pair, induced by the unit
of the realization/singular adjunction. -/
def cellRelJ (r : ℕ) :
    relChainCx ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) ⟶ relChainCx (stdCellPair.{u} r) :=
  relChainCxMap _ _ (sSetTopAdj.unit.app _) (sSetTopAdj.unit.app _)
    (sSetTopAdj.unit.naturality (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι)

/-- On the class of the identity `r`-simplex the single-cell comparison is the characteristic
relative chain. -/
theorem cellRelJ_topSimp (r : ℕ) :
    ((cellRelJ.{u} r).f r).hom
        (Submodule.Quotient.mk (Finsupp.single (topSimp.{u} r) (1 : ZMod 2)))
      = relCharChain.{u} r := by
  show Submodule.Quotient.mk
    (sSetChainMap (sSetTopAdj.unit.app (Δ[r] : SSet.{u})) r
      (Finsupp.single (topSimp.{u} r) (1 : ZMod 2))) = _
  rw [sSetChainMap_single]
  rfl

/-- The identity `r`-simplex is a relative simplicial cycle of `(Δ[r], ∂Δ[r])`. -/
theorem simplicialTop_mem_Zc (r : ℕ) :
    (Submodule.Quotient.mk (Finsupp.single (topSimp.{u} r) (1 : ZMod 2)) :
      RelChainMod ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) r)
      ∈ Zc (relChainCx ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι)) r := by
  match r with
  | 0 => exact mem_Zc_zero _
  | (m + 1) =>
      rw [mem_Zc_succ, relChainCx_d]
      show relBoundary _ m (Submodule.Quotient.mk _) = 0
      rw [relBoundary_mk]
      refine (Submodule.Quotient.mk_eq_zero _).2
        ⟨∑ i : Fin (m + 2), Finsupp.single (faceSimp.{u} m i) 1, ?_⟩
      rw [map_sum, sSetBoundary_single]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sSetChainMap_single]
      rfl

/-- **Optional corollary.**  The single-cell comparison sends the simplicial top generator to
the characteristic relative class `γ_r`. -/
theorem homologyMap_cellRelJ_top (r : ℕ) :
    (HomologicalComplex.homologyMap (cellRelJ.{u} r) r).hom
        (hcls (K := relChainCx ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι))
          (Submodule.Quotient.mk (Finsupp.single (topSimp.{u} r) (1 : ZMod 2)))
          (simplicialTop_mem_Zc.{u} r))
      = stdCellGenerator.{u} r := by
  rw [homologyMap_hcls]
  exact hcls_congr _ _ (cellRelJ_topSimp.{u} r)

end SpineTask20
