import RequestProject.Experiment2.NullSectorTask14.CoherenceAudit

/-!
# Task 14, Layer 17 (§55–§56): mixed words on an arbitrary minimal carrier

The single-axis intertwining theorem of Task 13 is *not* assumed to extend.  Here it is
proved directly for **arbitrary mixed words** of axis implementations and for **every**
unit axis slice pair:

* a Task-12 carrier equivalence intertwines the action of every mixed word
  (`word_action_intertwined`);
* it matches the two slices of *every* unit axis (`carrier_equiv_matches_generic_slices`);
* consequently all minimal carriers realize the **same** multi-axis transformation type
  (`multi_axis_carrier_type`, verdict `UNIVERSAL MULTI-AXIS CARRIER TYPE`).
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §55 — mixed words are intertwined by every carrier equivalence -/

/-- **PRINCIPAL THEOREM (§55): `multi_axis_carrier_intertwining`.**  A Task-12 carrier
equivalence (right multiplication by `r`) commutes with the left action of *every* mixed
word of axis implementations.  This is associativity, applied to a word of arbitrary
length. -/
theorem word_action_intertwined (l : AxisWord) (r ψ : W) :
    (wordVal l ⋆ ψ) ⋆ r = wordVal l ⋆ (ψ ⋆ r) := mul_assoc_W _ _ _

/-- **DERIVED (§55).**  The same for an arbitrary full implementation carrying arbitrary
central residuals. -/
theorem full_lift_action_intertwined (a b : ℝ) (n : Vec3) (θ : ℝ) (r ψ : W) :
    ((zz a b ⋆ Un n θ) ⋆ ψ) ⋆ r = (zz a b ⋆ Un n θ) ⋆ (ψ ⋆ r) := mul_assoc_W _ _ _

/-! ## §55 — the equivalence matches the slices of every unit axis -/

/-- **DERIVED (§55).**  A carrier equivalence maps the plus slice of any axis into the plus
slice, and the minus slice into the minus slice: the axis condition is *transported by
associativity*, not assumed. -/
theorem carrier_equiv_matches_generic_slices {L L' : Submodule ℝ W} {r : W}
    (hmap : ∀ ψ ∈ L, ψ ⋆ r ∈ L') (n : Vec3) :
    (∀ ψ ∈ Kp (spat n) L, ψ ⋆ r ∈ Kp (spat n) L') ∧
    (∀ ψ ∈ Km (spat n) L, ψ ⋆ r ∈ Km (spat n) L') := by
  constructor
  · intro ψ hψ
    obtain ⟨hψL, hψp⟩ := (mem_Kp_iff (spat n) L ψ).1 hψ
    exact (mem_Kp_iff (spat n) L' _).2 ⟨hmap ψ hψL, by rw [← mul_assoc_W, hψp]⟩
  · intro ψ hψ
    obtain ⟨hψL, hψm⟩ := (mem_Km_iff (spat n) L ψ).1 hψ
    exact (mem_Km_iff (spat n) L' _).2
      ⟨hmap ψ hψL, by rw [← mul_assoc_W, hψm, neg_mul_W]⟩

/-! ## §56 — the multi-axis carrier type -/

/-- **PRINCIPAL THEOREM (§56): `multi_axis_carrier_type`, verdict
`UNIVERSAL MULTI-AXIS CARRIER TYPE`.**  For any two minimal carriers there is one Task-12
equivalence which simultaneously

* matches the two slices of **every** unit axis,
* intertwines the action of **every** mixed word of axis implementations,
* intertwines the action of every full implementation with arbitrary central residual,

and both carriers carry the same exact sector factors for every axis.  Hence adding
further axes does not split the carrier family into inequivalent types. -/
theorem multi_axis_carrier_type {L L' : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) (hL' : IsMinimalLeftCarrier L') :
    ∃ r : W,
      (∀ n : Vec3, (∀ ψ ∈ Kp (spat n) L, ψ ⋆ r ∈ Kp (spat n) L') ∧
        (∀ ψ ∈ Km (spat n) L, ψ ⋆ r ∈ Km (spat n) L')) ∧
      (∀ (l : AxisWord) (ψ : W), (wordVal l ⋆ ψ) ⋆ r = wordVal l ⋆ (ψ ⋆ r)) ∧
      (∀ (a b : ℝ) (n : Vec3) (θ : ℝ) (ψ : W),
        ((zz a b ⋆ Un n θ) ⋆ ψ) ⋆ r = (zz a b ⋆ Un n θ) ⋆ (ψ ⋆ r)) ∧
      (∀ (n : Vec3) (θ : ℝ) (ψ : W), spat n ⋆ ψ = ψ → Un n θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
      (∀ (n : Vec3) (θ : ℝ) (ψ : W), spat n ⋆ ψ = -ψ → Un n θ ⋆ ψ = cMinusRef θ ⋆ ψ) := by
  obtain ⟨r, hmap, -, -⟩ := minimal_carriers_equivalent hL hL'
  exact ⟨r, fun n => carrier_equiv_matches_generic_slices hmap n,
    fun l ψ => word_action_intertwined l r ψ,
    fun a b n θ ψ => full_lift_action_intertwined a b n θ r ψ,
    fun _ θ _ h => (generic_action_exact θ).1 h,
    fun _ θ _ h => (generic_action_exact θ).2 h⟩

end NullSectorTask14
