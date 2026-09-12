import RequestProject.Experiment2.NullSectorTask14.AxisGeneratorMap

/-!
# Task 14, Phase II, Layer 12 (§35–§39): arbitrary unit spatial axes

Only now, with the intrinsic axis-to-generator map available, is an arbitrary unit spatial
direction admitted.  Its reference implementation is *constructed from the derived map*,
never from a conventional arbitrary-axis rotation formula, and everything about it — the
group law, the implemented automorphism, the carrier splitting, the reduced action — is
derived.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## Unit axes and their two derived elements -/

/-- **NEUTRAL DEFINITION (§35).**  A unit old spatial direction. -/
def IsUnitAxis (n : Vec3) : Prop := h3 n n = 1

theorem spat_sq_unit {n : Vec3} (hn : IsUnitAxis n) : spat n ⋆ spat n = w1 := by
  rw [spat_sq, hn, one_smul]

theorem Jmap_sq_unit {n : Vec3} (hn : IsUnitAxis n) : Jmap n ⋆ Jmap n = -w1 := by
  rw [Jmap_sq, hn]
  module

/-- **DERIVED.**  Existence of a unit spatial direction orthogonal to a given one:
constructed explicitly, with the two degenerate cases treated separately. -/
theorem exists_unit_orthogonal {n : Vec3} (hn : IsUnitAxis n) :
    ∃ m : Vec3, IsUnitAxis m ∧ h3 n m = 0 := by
  have hsum : n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
    have := hn
    simp only [IsUnitAxis, h3, dot3_apply] at this
    nlinarith [this]
  by_cases hcase : n.1 ^ 2 = 1
  · have h23 : n.2.1 ^ 2 + n.2.2 ^ 2 = 0 := by linarith
    have h2 : n.2.1 = 0 := by nlinarith [sq_nonneg n.2.1, sq_nonneg n.2.2]
    refine ⟨(0, 1, 0), ?_, ?_⟩
    · simp [IsUnitAxis, h3]
    · simp [h3, h2]
  · have hlt : n.1 ^ 2 < 1 := by
      rcases lt_trichotomy (n.1 ^ 2) 1 with h | h | h
      · exact h
      · exact absurd h hcase
      · nlinarith [sq_nonneg n.2.1, sq_nonneg n.2.2]
    set t : ℝ := 1 - n.1 ^ 2 with ht
    have htpos : 0 < t := by simp only [ht]; linarith
    have hsqrt : Real.sqrt t > 0 := Real.sqrt_pos.2 htpos
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt htpos)
    refine ⟨((1 - n.1 ^ 2) / Real.sqrt t, -(n.1 * n.2.1) / Real.sqrt t,
      -(n.1 * n.2.2) / Real.sqrt t), ?_, ?_⟩
    · simp only [IsUnitAxis, h3, dot3_apply]
      field_simp
      nlinarith [hsq, hsum]
    · simp only [h3, dot3_apply]
      field_simp
      first
        | linear_combination (-(n.1)) * hsum
        | linear_combination n.1 * hsum
        | nlinarith [hsum]

/-! ## §38 — the generic reference implementation -/

/-- **DERIVED (§38).**  The reference implementation attached to a unit axis, built from
the intrinsically derived axis-generator map.  No closed half-angle formula is prescribed
in advance: this is the unique continuation of the two basis-axis families already
derived. -/
noncomputable def Un (n : Vec3) (θ : ℝ) : W :=
  Real.cos (θ / 2) • w1 - Real.sin (θ / 2) • Jmap n

@[simp] theorem Un_zero (n : Vec3) : Un n 0 = w1 := by simp [Un]

theorem Un_neg (n : Vec3) (θ : ℝ) :
    Un n (-θ) = Real.cos (θ / 2) • w1 + Real.sin (θ / 2) • Jmap n := by
  rw [Un, show -θ / 2 = -(θ / 2) by ring, Real.cos_neg, Real.sin_neg]
  module

/-- **DERIVED.**  The multiplication rule of the two-plane spanned by the unit and a
square-minus-one direction. -/
theorem jsc_mul {j : W} (hj : j ⋆ j = -w1) (a b c d : ℝ) :
    (a • w1 - b • j) ⋆ (c • w1 - d • j)
      = (a * c - b * d) • w1 - (a * d + b * c) • j := by
  simp only [sub_mul_W, mul_sub_W, smul_mul_W, mul_smul_W, one_mul_W, mul_one_W, hj]
  module

/-- **PRINCIPAL THEOREM (§38): the group law of the generic reference family. -/
theorem Un_group {n : Vec3} (hn : IsUnitAxis n) (θ χ : ℝ) :
    Un n (θ + χ) = Un n θ ⋆ Un n χ := by
  have hJ := Jmap_sq_unit hn
  rw [Un, Un, Un, jsc_mul hJ, show (θ + χ) / 2 = θ / 2 + χ / 2 by ring,
    Real.cos_add, Real.sin_add]
  congr 1 <;> ring_nf

theorem Un_mul_neg {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : Un n θ ⋆ Un n (-θ) = w1 := by
  rw [← Un_group hn, add_neg_cancel, Un_zero]

theorem Un_neg_mul {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : Un n (-θ) ⋆ Un n θ = w1 := by
  rw [← Un_group hn, neg_add_cancel, Un_zero]

/-- **DERIVED (§38).**  The generic conjugation map. -/
noncomputable def PhiGen (n : Vec3) (θ : ℝ) : W →ₗ[ℝ] W where
  toFun x := (Un n θ ⋆ x) ⋆ Un n (-θ)
  map_add' := by
    intro x y
    simp only [mul_add_W, add_mul_W]
  map_smul' := by
    intro c x
    simp only [mul_smul_W, smul_mul_W, RingHom.id_apply]

@[simp] theorem PhiGen_apply (n : Vec3) (θ : ℝ) (x : W) :
    PhiGen n θ x = (Un n θ ⋆ x) ⋆ Un n (-θ) := rfl

/-- **PRINCIPAL THEOREM (§38).**  The generic conjugation is a unital algebra
automorphism. -/
theorem PhiGen_unital {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : PhiGen n θ w1 = w1 := by
  simp only [PhiGen_apply, mul_one_W]
  exact Un_mul_neg hn θ

theorem PhiGen_mul {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (x y : W) :
    PhiGen n θ (x ⋆ y) = PhiGen n θ x ⋆ PhiGen n θ y := by
  simp only [PhiGen_apply]
  have hinv : Un n (-θ) ⋆ Un n θ = w1 := Un_neg_mul hn θ
  calc (Un n θ ⋆ (x ⋆ y)) ⋆ Un n (-θ)
      = (Un n θ ⋆ (x ⋆ (w1 ⋆ y))) ⋆ Un n (-θ) := by rw [one_mul_W]
    _ = (Un n θ ⋆ (x ⋆ ((Un n (-θ) ⋆ Un n θ) ⋆ y))) ⋆ Un n (-θ) := by rw [hinv]
    _ = ((Un n θ ⋆ x) ⋆ Un n (-θ)) ⋆ ((Un n θ ⋆ y) ⋆ Un n (-θ)) := by
        simp only [mul_assoc_W]

theorem conj_assoc_helper (a b x c d : W) :
    ((a ⋆ b) ⋆ x) ⋆ (c ⋆ d) = (a ⋆ ((b ⋆ x) ⋆ c)) ⋆ d := by
  simp only [mul_assoc_W]

theorem PhiGen_group {n : Vec3} (hn : IsUnitAxis n) (θ χ : ℝ) (x : W) :
    PhiGen n (θ + χ) x = PhiGen n θ (PhiGen n χ x) := by
  simp only [PhiGen_apply]
  rw [Un_group hn θ χ, show -(θ + χ) = -χ + -θ by ring, Un_group hn (-χ) (-θ)]
  exact conj_assoc_helper (Un n θ) (Un n χ) x (Un n (-χ)) (Un n (-θ))

/-! ## §36, §37 — the generic carrier slices -/

/-- **PRINCIPAL THEOREM (§37): `generic_axis_carrier_split`.**  For **every** unit spatial
axis and **every** minimal left carrier the two slices are two-dimensional, intersect
trivially and span the carrier.  This no longer depends on the special basis axes. -/
theorem generic_carrier_split {n : Vec3} (hn : IsUnitAxis n) {L : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) :
    Kp (spat n) L ⊓ Km (spat n) L = ⊥ ∧
    Kp (spat n) L ⊔ Km (spat n) L = L ∧
    Module.finrank ℝ (Kp (spat n) L) = 2 ∧
    Module.finrank ℝ (Km (spat n) L) = 2 := by
  obtain ⟨m, hm, hnm⟩ := exists_unit_orthogonal hn
  have hanti : spat n ⋆ spat m = -(spat m ⋆ spat n) := spat_anticomm_of_orth hnm
  have hdims := finrank_slices (spat_sq_unit hn) (spat_sq_unit hm) hanti hL
  exact ⟨Kp_inf_Km (spat_sq_unit hn) L, Kp_sup_Km (spat_sq_unit hn) hL.1.1,
    hdims.1, hdims.2⟩

/-- **PRINCIPAL THEOREM (§36).**  Both generic slices are central lines: each is the
central plane of any of its nonzero elements. -/
theorem generic_slices_central_lines {n : Vec3} (hn : IsUnitAxis n) {L : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) {ψ χ : W} (hψ : ψ ∈ Kp (spat n) L) (hψ0 : ψ ≠ 0)
    (hχ : χ ∈ Km (spat n) L) (hχ0 : χ ≠ 0) :
    Kp (spat n) L = Zspan ψ ∧ Km (spat n) L = Zspan χ := by
  obtain ⟨-, -, hp, hm⟩ := generic_carrier_split hn hL
  exact ⟨central_line_of_finrank_two hp (fun _ h => wS_mul_mem_Kp hL.1.1 h) hψ hψ0,
    central_line_of_finrank_two hm (fun _ h => wS_mul_mem_Km hL.1.1 h) hχ hχ0⟩

/-! ## §39 — the generic reduced action -/

/-- **DERIVED (§39).**  On the plus slice of a generic axis the derived generator direction
acts as the central element. -/
theorem Jmap_mul_of_mem_Kp_gen {n : Vec3} {ψ : W} (hψ : spat n ⋆ ψ = ψ) :
    Jmap n ⋆ ψ = wS ⋆ ψ := by
  rw [Jmap_eq_central_mul, mul_assoc_W, hψ]

theorem Jmap_mul_of_mem_Km_gen {n : Vec3} {ψ : W} (hψ : spat n ⋆ ψ = -ψ) :
    Jmap n ⋆ ψ = -(wS ⋆ ψ) := by
  rw [Jmap_eq_central_mul, mul_assoc_W, hψ, mul_neg_W]

/-- **PRINCIPAL THEOREM (§39): `generic_axis_reference_action`.**  The generic reduced
action on the two slices is by exactly the same two central factors as for the two basis
axes. -/
theorem generic_action_exact {n : Vec3} {ψ : W} (θ : ℝ) :
    (spat n ⋆ ψ = ψ → Un n θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
    (spat n ⋆ ψ = -ψ → Un n θ ⋆ ψ = cMinusRef θ ⋆ ψ) := by
  constructor
  · intro hp
    rw [Un, sub_mul_W, smul_mul_W, smul_mul_W, one_mul_W, Jmap_mul_of_mem_Kp_gen hp,
      cPlusRef, zz_mul]
    module
  · intro hm
    rw [Un, sub_mul_W, smul_mul_W, smul_mul_W, one_mul_W, Jmap_mul_of_mem_Km_gen hm,
      cMinusRef, zz_mul]
    module

/-- **PRINCIPAL THEOREM (§39): `generic_axis_relative_action`, verdict
**UNIVERSAL ALL-AXIS RELATIVE LAW**.**  For every unit axis, every minimal carrier and
every parameter the relative factor between the two slices is the *same* fixed central
element `Rel(θ) = cos θ • 1 − sin θ • S`, already obtained for the two basis axes. -/
theorem generic_relative_action_universal (θ : ℝ) :
    cPlusRef θ = RelRef θ ⋆ cMinusRef θ ∧
    (∀ (n : Vec3) (ψ : W), spat n ⋆ ψ = ψ → Un n θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
    (∀ (n : Vec3) (ψ : W), spat n ⋆ ψ = -ψ → Un n θ ⋆ ψ = cMinusRef θ ⋆ ψ) :=
  ⟨(reference_relative_action_exact θ).2.1,
    fun _ _ h => (generic_action_exact θ).1 h,
    fun _ _ h => (generic_action_exact θ).2 h⟩

/-- **DERIVED (§38).**  The generic reference action preserves every left carrier and both
of its generic slices. -/
theorem generic_preserves_slices {n : Vec3} {L : Submodule ℝ W} (hL : IsLeftCarrier L)
    (θ : ℝ) :
    (∀ ψ ∈ Kp (spat n) L, Un n θ ⋆ ψ ∈ Kp (spat n) L) ∧
    (∀ ψ ∈ Km (spat n) L, Un n θ ⋆ ψ ∈ Km (spat n) L) := by
  constructor
  · intro ψ hψ
    rw [(generic_action_exact θ).1 hψ.2]
    exact Kp_central_stable hL (cPlusRef_mem_Z θ) hψ
  · intro ψ hψ
    rw [(generic_action_exact θ).2 hψ.2]
    exact Km_central_stable hL (cMinusRef_mem_Z θ) hψ

end NullSectorTask14
