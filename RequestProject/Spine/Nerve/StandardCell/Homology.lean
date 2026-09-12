import RequestProject.Spine.Nerve.StandardCell.Pair
import RequestProject.Spine.Nerve.StandardCell.BoundaryHomology

/-!
# Task 19, WP8–WP9 : the relative homology of the standard cell pair, and blocker B1

Combining

* Task 17's closed embedding `|∂Δ[r]| ↪ |Δ[r]|` and contractibility of `|Δ[r]|`,
* Task 18's vanishing of positive singular homology of a contractible space,
* the WP7 computation of `H_*(|∂Δ[r]|;ℤ₂)`,

through the Task-14 long exact sequence of a pair gives the complete computation of
`H_*(|Δ[r]|,|∂Δ[r]|;ℤ₂)` and closes blocker B1:

* `SpineTask19.standardCellPairAcyclic`;
* `SpineTask19.standardCellPairTop`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial SSet NerveGeom SpineTask14 SpineTask18

universe u

namespace SpineTask19

/-! ## The standard cell pair -/

/-- The realized standard simplex `|Δ[r]|`. -/
abbrev Cell (r : ℕ) : TopCat.{u} := SSet.toTop.{u}.obj (Δ[r] : SSet.{u})

/-- The realized boundary inclusion `|∂Δ[r]| ⟶ |Δ[r]|`. -/
abbrev cellIncl (r : ℕ) : Bd.{u} r ⟶ Cell.{u} r :=
  SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι

theorem cellIncl_injective (r : ℕ) : Function.Injective (cellIncl.{u} r) :=
  (SpineTask17.isClosedEmbedding_realization_boundary.{u} r).injective

theorem stdCellPair_injective (r : ℕ) (n) : Function.Injective ((stdCellPair.{u} r).app n) :=
  toSSet_map_injective (cellIncl.{u} r) (cellIncl_injective.{u} r) n

/-- `H_q(|Δ[r]|;ℤ₂) = 0` in positive degrees. -/
theorem isZero_cell_homology (r q : ℕ) : IsZero ((singCx (Cell.{u} r)).homology (q + 1)) :=
  isZero_homology_of_contractible (X := Cell.{u} r) q

/-! ## The bottom of the pair sequence -/

theorem epi_pProj_zero {S T : SSet.{u}} (f : S ⟶ T) : Epi (pProj f 0) := by
  refine (ModuleCat.epi_iff_surjective _).2 fun t => ?_
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (sSetChainMap f 0)) z
  exact ⟨hcls (K := sSetChainComplexFunctor.obj T) w (mem_Zc_zero w),
    by rw [homologyMap_hcls]; exact hcls_congr _ _ (relProj_f_apply f 0 w)⟩

theorem pIota_comp_pProj {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) :
    (pIota f q) ≫ (pProj f q) = 0 := by
  have h : sSetChainComplexFunctor.map f ≫ relProj f = 0 := (relSC f).zero
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_zero]

/-! ## The relative homology of the standard cell pair -/

section Pair

variable (r : ℕ)

/-- `H_{q+2}(|Δ[r]|,|∂Δ[r]|) ≅ H_{q+1}(|∂Δ[r]|)`. -/
def relIsoBd (q : ℕ) :
    relHomology (stdCellPair.{u} r) (q + 2) ≅ (singCx (Bd.{u} r)).homology (q + 1) :=
  haveI : IsIso (pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) (q + 1)) :=
    isIso_pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) (q + 1)
      (isZero_cell_homology.{u} r (q + 1)) (isZero_cell_homology.{u} r q)
  asIso (pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) (q + 1))

/-- `H₁(|Δ[r]|,|∂Δ[r]|) ≃ H̃₀(|∂Δ[r]|)`. -/
def relEquivOneBd : relHomology (stdCellPair.{u} r) 1 ≃ₗ[ZMod 2] Hred0 (Bd.{u} r) := by
  classical
  have t₀ : ↥(Cell.{u} r) := Classical.arbitrary _
  have hmono : Function.Injective
      ((pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) 0).hom) :=
    (ModuleCat.mono_iff_injective _).1
      (mono_pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) 0
        (isZero_cell_homology.{u} r 0))
  have hrange : LinearMap.range
      ((pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) 0).hom)
      = Hred0 (Bd.{u} r) := by
    rw [range_pairDelta (stdCellPair.{u} r) (stdCellPair_injective.{u} r) 0]
    exact ker_homologyMap_zero_eq_Hred0 (cellIncl.{u} r) t₀
  exact (LinearEquiv.ofInjective _ hmono).trans (LinearEquiv.ofEq _ _ hrange)

/-- In degree `0` the relative homology of a nonempty cell pair vanishes. -/
theorem isZero_rel_zero (s₀ : ↥(Bd.{u} r)) :
    IsZero (relHomology (stdCellPair.{u} r) 0) := by
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun t => ?_)
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (epi_pProj_zero (stdCellPair.{u} r)) t
  obtain ⟨z, hz, rfl⟩ := hcls_surjective y
  set t₀ : ↥(Cell.{u} r) := (ConcreteCategory.hom (cellIncl.{u} r)) s₀ with ht₀
  have hkey : (pProj (stdCellPair.{u} r) 0).hom (ptCls (Cell.{u} r) t₀) = 0 := by
    rw [ht₀, ← homologyMap_ptCls (cellIncl.{u} r) s₀]
    exact congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom
      (pIota_comp_pProj (stdCellPair.{u} r) 0))) (ptCls (Bd.{u} r) s₀)
  rw [show hcls (K := singCx (Cell.{u} r)) z hz
      = (augS (Cell.{u} r) 0 z) • ptCls (Cell.{u} r) t₀ from
    hcls_zero_eq_augS_smul t₀ z, map_smul, hkey, smul_zero]

end Pair

/-! ## Auxiliary transfers -/

theorem isZero_of_equiv_subsingleton {M : ModuleCat.{u} (ZMod 2)} {N : Type*} [AddCommGroup N]
    [Module (ZMod 2) N] [Subsingleton N] (e : M ≃ₗ[ZMod 2] N) : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton

theorem subsingleton_Hred0_of_isZero {X : TopCat.{u}} (h : IsZero ((singCx X).homology 0)) :
    Subsingleton (Hred0 X) := by
  haveI : Subsingleton ((singCx X).homology 0) := ModuleCat.isZero_iff_subsingleton.1 h
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

theorem subsingleton_Hred0_Bd_succ (n : ℕ) : Subsingleton (Hred0 (Bd.{u} (n + 2))) := by
  rw [Hred0_Bd_eq_bot n]
  infer_instance

/-! ## WP9 : the Task-14 blocker propositions -/

/-- **WP9, vanishing part.**  `H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂) = 0` for `q ≠ r`. -/
theorem standardCellPairAcyclic (r : ℕ) : SpineTask14.StandardCellPairAcyclic.{u} r := by
  intro q hqr
  rcases r with _ | r
  · -- `r = 0` : the boundary is empty
    rcases q with _ | _ | m
    · exact absurd rfl hqr
    · haveI := subsingleton_Hred0_of_isZero (X := Bd.{u} 0) (isZero_homology_of_isEmpty 0)
      exact isZero_of_equiv_subsingleton (relEquivOneBd.{u} 0)
    · exact IsZero.of_iso (isZero_homology_of_isEmpty (m + 1)) (relIsoBd.{u} 0 m)
  · -- `r ≥ 1` : the boundary is nonempty
    have hs₀ : Nonempty ↥(Bd.{u} (r + 1)) := by
      rcases r with _ | k
      · exact ⟨bdOnePt.{u} 0⟩
      · infer_instance
    obtain ⟨s₀⟩ := hs₀
    rcases q with _ | _ | m
    · exact isZero_rel_zero.{u} (r + 1) s₀
    · -- degree one, `r ≠ 1`
      rcases r with _ | k
      · exact absurd rfl hqr
      · haveI := subsingleton_Hred0_Bd_succ.{u} k
        exact isZero_of_equiv_subsingleton (relEquivOneBd.{u} (k + 2))
    · refine IsZero.of_iso ?_ (relIsoBd.{u} (r + 1) m)
      exact bd_isZero (r + 1) (m + 1) (by omega) (by omega) (by omega)

/-- **WP9, top part.**  `H_r^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)` is one-dimensional. -/
theorem isLine_relHomology_top (r : ℕ) :
    IsLine (relHomology (stdCellPair.{u} r) r) := by
  rcases r with _ | r
  · -- `r = 0`
    have t₀ : ↥(Cell.{u} 0) := Classical.arbitrary _
    haveI : Mono (pProj (stdCellPair.{u} 0) 0) :=
      (pair_exact₂ (stdCellPair.{u} 0) (stdCellPair_injective.{u} 0) 0).mono_g
        ((isZero_homology_of_isEmpty (X := Bd.{u} 0) 0).eq_zero_of_src _)
    haveI : Epi (pProj (stdCellPair.{u} 0) 0) := epi_pProj_zero (stdCellPair.{u} 0)
    haveI : IsIso (pProj (stdCellPair.{u} 0) 0) := isIso_of_mono_of_epi _
    have hline : IsLine ((singCx (Cell.{u} 0)).homology 0) := ⟨h0Equiv t₀⟩
    exact IsLine.of_iso hline (asIso (pProj (stdCellPair.{u} 0) 0))
  · rcases r with _ | k
    · -- `r = 1`
      exact IsLine.congr isLine_Hred0_Bd_one (relEquivOneBd.{u} 1).symm
    · -- `r ≥ 2`
      refine IsLine.of_iso ?_ (relIsoBd.{u} (k + 2) k).symm
      have h := bd_isLine_top.{u} (k + 2) (by omega)
      simpa using h

/-- **WP9, top part, in the exact Task-14 form.** -/
theorem standardCellPairTop (r : ℕ) : SpineTask14.StandardCellPairTop.{u} r :=
  (isLine_relHomology_top.{u} r).nonempty_iso

end SpineTask19
