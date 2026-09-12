import RequestProject.Spine.Nerve.StandardCell.Homology

/-!
# Task 19, WP6 : the canonical mod-2 fundamental classes

Over `ℤ₂` a one-dimensional vector space has exactly **one** nonzero element, so a
distinguished top class needs no orientation choice: it is the unique nonzero element.  This
module makes that precise (`lineGen`), and uses it to define

* `SpineTask19.bdFundClass r` — the distinguished class `β_r ∈ H_{r-1}(|∂Δ[r]|;ℤ₂)`, defined
  by the two point classes for `r = 1` and as the unique nonzero top class for `r ≥ 2`;
* `SpineTask19.stdCellTopClass r` — the distinguished generator of
  `H_r(|Δ[r]|,|∂Δ[r]|;ℤ₂)`;
* `SpineTask19.stdCellTopEquiv r` — the resulting linear equivalence with `ℤ₂`, sending the
  generator to `1`.

The recursive Mayer–Vietoris relation of WP6 and the pair-connecting relation of WP7 are proved
by uniqueness of the nonzero element of a line.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial SSet NerveGeom SpineTask14 SpineTask18

universe u

namespace SpineTask19

/-! ## The unique nonzero element of a line -/

variable {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N] [Module (ZMod 2) N]

/-- A chosen linear equivalence `M ≃ ℤ₂` for a one-dimensional `M`. -/
def lineEquiv (h : IsLine M) : M ≃ₗ[ZMod 2] ZMod 2 := h.some

/-- **The** generator of a one-dimensional `ℤ₂`-vector space: its unique nonzero element. -/
def lineGen (h : IsLine M) : M := (lineEquiv h).symm 1

theorem lineEquiv_lineGen (h : IsLine M) : lineEquiv h (lineGen h) = 1 :=
  (lineEquiv h).apply_symm_apply 1

theorem lineGen_ne_zero (h : IsLine M) : lineGen h ≠ 0 := by
  intro hz
  have := lineEquiv_lineGen h
  rw [hz, map_zero] at this
  exact zero_ne_one this

theorem eq_lineGen_of_ne_zero (h : IsLine M) {x : M} (hx : x ≠ 0) : x = lineGen h := by
  refine (lineEquiv h).injective ?_
  rw [lineEquiv_lineGen]
  have h0 : lineEquiv h x ≠ 0 := fun hc => hx ((lineEquiv h).injective (by rw [hc, map_zero]))
  revert h0
  generalize lineEquiv h x = a
  revert a
  decide

theorem eq_zero_or_eq_lineGen (h : IsLine M) (x : M) : x = 0 ∨ x = lineGen h := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (eq_lineGen_of_ne_zero h hx)

theorem exists_smul_lineGen (h : IsLine M) (x : M) : ∃ a : ZMod 2, x = a • lineGen h := by
  rcases eq_zero_or_eq_lineGen h x with hx | hx
  · exact ⟨0, by rw [hx, zero_smul]⟩
  · exact ⟨1, by rw [hx, one_smul]⟩

/-! ## WP6/WP7 : the distinguished boundary class `β_r` -/

/-- **WP7.**  The distinguished class `β_r ∈ H_{r-1}(|∂Δ[r]|;ℤ₂)`.  For `r = 1` it is the sum
of the two point classes of `S⁰`; for `r ≥ 2` it is the unique nonzero element of the
one-dimensional top homology.  (For `r = 0` the group is zero.) -/
def bdFundClass : (r : ℕ) → (singCx (Bd.{u} r)).homology (r - 1)
  | 0 => 0
  | 1 => ptCls (Bd.{u} 1) (bdOnePt.{u} 0) + ptCls (Bd.{u} 1) (bdOnePt.{u} 1)
  | (k + 2) => lineGen (bd_isLine_top.{u} (k + 2) (by omega))

theorem bdFundClass_one_mem : bdFundClass.{u} 1 ∈ Hred0 (Bd.{u} 1) :=
  sum_ptCls_mem _ _

theorem bdFundClass_ne_zero : ∀ (r : ℕ), r ≠ 0 → bdFundClass.{u} r ≠ 0
  | 0, h => absurd rfl h
  | 1, _ => by
    intro hz
    have h1 : (1 : ZMod 2) • ptCls (Bd.{u} 1) (bdOnePt.{u} 0)
        + (1 : ZMod 2) • ptCls (Bd.{u} 1) (bdOnePt.{u} 1) = 0 := by
      rw [one_smul, one_smul]
      exact hz
    exact one_ne_zero (h0_two_indep _ _ bdOnePt_ne 1 1 h1).1
  | (k + 2), _ => lineGen_ne_zero _

theorem bdFundClass_eq_lineGen (k : ℕ) :
    bdFundClass.{u} (k + 2) = lineGen (bd_isLine_top.{u} (k + 2) (by omega)) := rfl

/-! ## WP6 : the recursive Mayer–Vietoris relation -/

/-- The Mayer–Vietoris isomorphism carries `β_{k+3}` to `β_{k+2}`. -/
theorem bdIsoSucc_bdFundClass (k : ℕ) :
    (bdIsoSucc.{u} (k + 1) k).hom.hom (bdFundClass.{u} (k + 3)) = bdFundClass.{u} (k + 2) := by
  refine (eq_lineGen_of_ne_zero (bd_isLine_top.{u} (k + 2) (by omega)) ?_).trans
    (bdFundClass_eq_lineGen.{u} k).symm
  intro hz
  refine bdFundClass_ne_zero.{u} (k + 3) (by omega) ?_
  have hinj : Function.Injective ((bdIsoSucc.{u} (k + 1) k).hom.hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact hinj (by rw [hz, map_zero])

/-- In the transition `S⁰ ⇝ S¹` the Mayer–Vietoris identification carries `β_2` to `β_1`. -/
theorem bdEquivOne_bdFundClass :
    ((bdEquivOne.{u} 0) (bdFundClass.{u} 2) : (singCx (Bd.{u} 1)).homology 0)
      = bdFundClass.{u} 1 := by
  have hline : IsLine (Hred0 (Bd.{u} 1)) := isLine_Hred0_Bd_one
  have h1 : (⟨bdFundClass.{u} 1, bdFundClass_one_mem⟩ : Hred0 (Bd.{u} 1)) ≠ 0 := by
    intro hc
    exact bdFundClass_ne_zero.{u} 1 (by omega) (congrArg Subtype.val hc)
  have h2 : (bdEquivOne.{u} 0) (bdFundClass.{u} 2) ≠ 0 := by
    intro hc
    exact bdFundClass_ne_zero.{u} 2 (by omega)
      ((bdEquivOne.{u} 0).injective (by rw [hc, map_zero]))
  rw [eq_lineGen_of_ne_zero hline h2, ← eq_lineGen_of_ne_zero hline h1]

/-! ## The canonical generator of the top relative homology -/

/-- **The** generator of `H_r(|Δ[r]|,|∂Δ[r]|;ℤ₂)`: its unique nonzero element. -/
def stdCellTopClass (r : ℕ) : relHomology (stdCellPair.{u} r) r :=
  lineGen (isLine_relHomology_top.{u} r)

theorem stdCellTopClass_ne_zero (r : ℕ) : stdCellTopClass.{u} r ≠ 0 :=
  lineGen_ne_zero _

theorem eq_zero_or_eq_stdCellTopClass (r : ℕ) (x : relHomology (stdCellPair.{u} r) r) :
    x = 0 ∨ x = stdCellTopClass.{u} r :=
  eq_zero_or_eq_lineGen _ x

theorem exists_smul_stdCellTopClass (r : ℕ) (x : relHomology (stdCellPair.{u} r) r) :
    ∃ a : ZMod 2, x = a • stdCellTopClass.{u} r :=
  exists_smul_lineGen _ x

/-- **The required interface.**  A linear equivalence
`H_r(|Δ[r]|,|∂Δ[r]|;ℤ₂) ≃ ℤ₂` sending the canonical generator to `1`. -/
def stdCellTopEquiv (r : ℕ) : relHomology (stdCellPair.{u} r) r ≃ₗ[ZMod 2] ZMod 2 :=
  lineEquiv (isLine_relHomology_top.{u} r)

@[simp] theorem stdCellTopEquiv_stdCellTopClass (r : ℕ) :
    stdCellTopEquiv.{u} r (stdCellTopClass.{u} r) = 1 :=
  lineEquiv_lineGen _

/-! ## WP7 : the connecting map sends the top generator to `β_r` -/

/-- For `r ≥ 2` the pair connecting isomorphism carries the top relative generator to the
distinguished boundary class. -/
theorem pairDelta_stdCellTopClass_succ (k : ℕ) :
    (pairDelta (stdCellPair.{u} (k + 2)) (stdCellPair_injective.{u} (k + 2)) (k + 1)).hom
        (stdCellTopClass.{u} (k + 2))
      = bdFundClass.{u} (k + 2) := by
  haveI : IsIso (pairDelta (stdCellPair.{u} (k + 2)) (stdCellPair_injective.{u} (k + 2)) (k + 1)) :=
    isIso_pairDelta (stdCellPair.{u} (k + 2)) (stdCellPair_injective.{u} (k + 2)) (k + 1)
      (isZero_cell_homology.{u} (k + 2) (k + 1)) (isZero_cell_homology.{u} (k + 2) k)
  have hinj : Function.Injective
      ((pairDelta (stdCellPair.{u} (k + 2)) (stdCellPair_injective.{u} (k + 2)) (k + 1)).hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine (eq_lineGen_of_ne_zero (bd_isLine_top.{u} (k + 2) (by omega)) ?_).trans
    (bdFundClass_eq_lineGen.{u} k).symm
  intro hz
  exact stdCellTopClass_ne_zero.{u} (k + 2) (hinj (by rw [hz, map_zero]))

/-- For `r = 1` the pair connecting map carries the top relative generator to `β_1`, the sum of
the two point classes of `|∂Δ[1]|`. -/
theorem pairDelta_stdCellTopClass_one :
    (pairDelta (stdCellPair.{u} 1) (stdCellPair_injective.{u} 1) 0).hom
        (stdCellTopClass.{u} 1)
      = bdFundClass.{u} 1 := by
  have hmono : Function.Injective
      ((pairDelta (stdCellPair.{u} 1) (stdCellPair_injective.{u} 1) 0).hom) :=
    (ModuleCat.mono_iff_injective _).1
      (mono_pairDelta (stdCellPair.{u} 1) (stdCellPair_injective.{u} 1) 0
        (isZero_cell_homology.{u} 1 0))
  have hmem : (pairDelta (stdCellPair.{u} 1) (stdCellPair_injective.{u} 1) 0).hom
      (stdCellTopClass.{u} 1) ∈ Hred0 (Bd.{u} 1) := by
    have t₀ : ↥(Cell.{u} 1) := Classical.arbitrary _
    have hrange := range_pairDelta (stdCellPair.{u} 1) (stdCellPair_injective.{u} 1) 0
    rw [ker_homologyMap_zero_eq_Hred0 (cellIncl.{u} 1) t₀] at hrange
    rw [← hrange]
    exact ⟨_, rfl⟩
  have hne : (⟨_, hmem⟩ : Hred0 (Bd.{u} 1)) ≠ 0 := by
    intro hc
    refine stdCellTopClass_ne_zero.{u} 1 (hmono ?_)
    rw [map_zero]
    exact congrArg Subtype.val hc
  have h1 : (⟨bdFundClass.{u} 1, bdFundClass_one_mem⟩ : Hred0 (Bd.{u} 1)) ≠ 0 := by
    intro hc
    exact bdFundClass_ne_zero.{u} 1 (by omega) (congrArg Subtype.val hc)
  have := (eq_lineGen_of_ne_zero isLine_Hred0_Bd_one hne).trans
    (eq_lineGen_of_ne_zero isLine_Hred0_Bd_one h1).symm
  exact congrArg Subtype.val this

end SpineTask19
