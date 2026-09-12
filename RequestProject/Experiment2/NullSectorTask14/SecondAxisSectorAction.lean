import RequestProject.Experiment2.NullSectorTask14.SecondAxisCarrierSlices

/-!
# Task 14, Layer 5 (§17, §18): the reduced second-axis action and the relative sector law

The independently reconstructed second-axis reference implementer is restricted to an
arbitrary minimal carrier.  Nothing is assumed about the resulting factors: they are
derived from the second-axis sector relations

`Q ⋆ ψ = -(S ⋆ ψ)` on the plus sector,  `Q ⋆ ψ = S ⋆ ψ` on the minus sector,

which in turn follow from `S ⋆ B = -Q` and centrality of `S`.

Only in the last group of theorems (§18) is the outcome *compared* with the inherited
A-axis result.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## The derived second-axis sector relations -/

/-- **DERIVED (§17).**  On the second-axis plus sector the derived generator direction acts
as minus the central element. -/
theorem wQ_mul_of_mem_HBplus {ψ : W} (hψ : ψ ∈ HBplus) : wQ ⋆ ψ = -(wS ⋆ ψ) := by
  have hB : wB ⋆ ψ = ψ := hψ
  have : wS ⋆ (wB ⋆ ψ) = wS ⋆ ψ := by rw [hB]
  rw [← mul_assoc_W, wit8_wS_wB, neg_mul_W] at this
  rw [← neg_eq_iff_eq_neg]
  exact this

/-- **DERIVED (§17).**  On the second-axis minus sector it acts as the central element. -/
theorem wQ_mul_of_mem_HBminus {ψ : W} (hψ : ψ ∈ HBminus) : wQ ⋆ ψ = wS ⋆ ψ := by
  have hB : wB ⋆ ψ = -ψ := hψ
  have h : wS ⋆ (wB ⋆ ψ) = wS ⋆ (-ψ) := by rw [hB]
  rw [← mul_assoc_W, wit8_wS_wB, neg_mul_W, mul_neg_W] at h
  exact neg_injective h

/-! ## §17 — the exact reduced action -/

/-- **DERIVED (§17).**  The central factor of the second-axis reference action on the plus
slice. -/
noncomputable def cBplus (φ : ℝ) : W := zz (Real.cos (φ / 2)) (-Real.sin (φ / 2))

/-- **DERIVED (§17).**  The central factor on the minus slice. -/
noncomputable def cBminus (φ : ℝ) : W := zz (Real.cos (φ / 2)) (Real.sin (φ / 2))

theorem cBplus_mem_Z (φ : ℝ) : cBplus φ ∈ Z := zz_mem_Z _ _
theorem cBminus_mem_Z (φ : ℝ) : cBminus φ ∈ Z := zz_mem_Z _ _

/-- **PRINCIPAL THEOREM (§17): `second_axis_sector_action_exact` (plus).**  On the whole
second-axis plus sector — in particular on the plus slice of an arbitrary minimal carrier —
the derived reference implementer acts by the central factor `cos(φ/2)•1 − sin(φ/2)•S`. -/
theorem second_axis_action_plus_exact {ψ : W} (hψ : ψ ∈ HBplus) (φ : ℝ) :
    UBref φ ⋆ ψ = cBplus φ ⋆ ψ := by
  rw [UBref_apply, add_mul_W, smul_mul_W, smul_mul_W, one_mul_W, cBplus, zz_mul,
    wQ_mul_of_mem_HBplus hψ]
  module

/-- **PRINCIPAL THEOREM (§17): `second_axis_sector_action_exact` (minus).**  Independently
derived on the minus sector: the central factor is `cos(φ/2)•1 + sin(φ/2)•S`. -/
theorem second_axis_action_minus_exact {ψ : W} (hψ : ψ ∈ HBminus) (φ : ℝ) :
    UBref φ ⋆ ψ = cBminus φ ⋆ ψ := by
  rw [UBref_apply, add_mul_W, smul_mul_W, smul_mul_W, one_mul_W, cBminus, zz_mul,
    wQ_mul_of_mem_HBminus hψ]

/-! ## Sector invariance of the reduced action -/

theorem Kp_central_stable {n : W} {L : Submodule ℝ W} (hL : IsLeftCarrier L) {z : W}
    (hz : z ∈ Z) {ψ : W} (hψ : ψ ∈ Kp n L) : z ⋆ ψ ∈ Kp n L := by
  refine ⟨hL z ψ hψ.1, ?_⟩
  show n ⋆ (z ⋆ ψ) = z ⋆ ψ
  rw [← mul_assoc_W, ← comm_all_of_mem_Z hz n, mul_assoc_W, hψ.2]

theorem Km_central_stable {n : W} {L : Submodule ℝ W} (hL : IsLeftCarrier L) {z : W}
    (hz : z ∈ Z) {ψ : W} (hψ : ψ ∈ Km n L) : z ⋆ ψ ∈ Km n L := by
  refine ⟨hL z ψ hψ.1, ?_⟩
  show n ⋆ (z ⋆ ψ) = -(z ⋆ ψ)
  rw [← mul_assoc_W, ← comm_all_of_mem_Z hz n, mul_assoc_W, hψ.2, mul_neg_W]

/-- **PRINCIPAL THEOREM (§17).**  The reduced second-axis action maps each slice of an
arbitrary left carrier **onto** itself. -/
theorem second_axis_preserves_slices {L : Submodule ℝ W} (hL : IsLeftCarrier L) (φ : ℝ) :
    Submodule.map (Lmul (UBref φ)) (KBplus L) = KBplus L ∧
    Submodule.map (Lmul (UBref φ)) (KBminus L) = KBminus L := by
  constructor
  · ext χ
    simp only [Submodule.mem_map, Lmul_apply]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      rw [second_axis_action_plus_exact hψ.2]
      exact Kp_central_stable hL (cBplus_mem_Z φ) hψ
    · intro hχ
      refine ⟨UBref (-φ) ⋆ χ, ?_, ?_⟩
      · rw [second_axis_action_plus_exact hχ.2]
        exact Kp_central_stable hL (cBplus_mem_Z (-φ)) hχ
      · rw [← mul_assoc_W, UBref_mul_neg, one_mul_W]
  · ext χ
    simp only [Submodule.mem_map, Lmul_apply]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      rw [second_axis_action_minus_exact hψ.2]
      exact Km_central_stable hL (cBminus_mem_Z φ) hψ
    · intro hχ
      refine ⟨UBref (-φ) ⋆ χ, ?_, ?_⟩
      · rw [second_axis_action_minus_exact hχ.2]
        exact Km_central_stable hL (cBminus_mem_Z (-φ)) hχ
      · rw [← mul_assoc_W, UBref_mul_neg, one_mul_W]

/-! ## §18 — the relative sector theorem for the second axis -/

/-- **DERIVED (§18).**  The intrinsic relative factor of the second-axis reduced action. -/
noncomputable def RelB (φ : ℝ) : W := zz (Real.cos φ) (-Real.sin φ)

theorem RelB_mem_Z (φ : ℝ) : RelB φ ∈ Z := zz_mem_Z _ _

/-- **PRINCIPAL THEOREM (§18): `second_axis_relative_action_exact`.**  The two second-axis
sector factors are mutually inverse central units, and the division-free relative identity
`c₊ = Rel ⋆ c₋` holds with `Rel(φ) = cos φ • 1 − sin φ • S`, which is the square of the
plus factor. -/
theorem second_axis_relative_action_exact (φ : ℝ) :
    cBplus φ ⋆ cBminus φ = w1 ∧
    cBminus φ ⋆ cBplus φ = w1 ∧
    cBplus φ = RelB φ ⋆ cBminus φ ∧
    RelB φ = cBplus φ ⋆ cBplus φ := by
  have hpy := Real.sin_sq_add_cos_sq (φ / 2)
  have hh : φ = 2 * (φ / 2) := by ring
  have hc : Real.cos φ = Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 := by
    conv_lhs => rw [hh]
    rw [Real.cos_two_mul']
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    conv_lhs => rw [hh]
    rw [Real.sin_two_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cBplus, cBminus, zz_mul_zz, ← zz_one_zero]
    congr 1 <;> nlinarith [hpy]
  · rw [cBplus, cBminus, zz_mul_zz, ← zz_one_zero]
    congr 1 <;> nlinarith [hpy]
  · rw [cBplus, cBminus, RelB, zz_mul_zz, hc, hs]
    congr 1 <;>
      first
        | linear_combination (0 : ℝ) * hpy
        | linear_combination (Real.cos (φ / 2)) * hpy
        | linear_combination (-(Real.cos (φ / 2))) * hpy
        | linear_combination (Real.sin (φ / 2)) * hpy
        | linear_combination (-(Real.sin (φ / 2))) * hpy
  · rw [cBplus, RelB, zz_mul_zz, hc, hs]
    congr 1 <;>
      first
        | linear_combination (0 : ℝ) * hpy
        | linear_combination (Real.cos (φ / 2)) * hpy
        | linear_combination (-(Real.cos (φ / 2))) * hpy
        | linear_combination (Real.sin (φ / 2)) * hpy
        | linear_combination (-(Real.sin (φ / 2))) * hpy

/-- **PRINCIPAL THEOREM (§18): the relative law is independent of the implementation and
of the carrier.**  For an *arbitrary* second-axis implementer `V` the two sector factors
are the reference ones multiplied by one and the same central element; consequently the
division-free relative factor is the fixed `Rel(φ)`, independent of the implementation, of
the residual central freedom, and of the literal carrier. -/
theorem second_axis_relative_action_independent {V : ℝ → W} (hV : IsBLift V) (φ : ℝ) :
    ∃ z ∈ Z,
      (∀ ψ ∈ HBplus, V φ ⋆ ψ = (z ⋆ cBplus φ) ⋆ ψ) ∧
      (∀ ψ ∈ HBminus, V φ ⋆ ψ = (z ⋆ cBminus φ) ⋆ ψ) ∧
      z ⋆ cBplus φ = RelB φ ⋆ (z ⋆ cBminus φ) := by
  obtain ⟨z, hz, hVz⟩ := bLift_relative_factor hV UBref_isBLift φ
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · intro ψ hψ
    rw [hVz, mul_assoc_W, second_axis_action_plus_exact hψ, mul_assoc_W]
  · intro ψ hψ
    rw [hVz, mul_assoc_W, second_axis_action_minus_exact hψ, mul_assoc_W]
  · have h := (second_axis_relative_action_exact φ).2.2.1
    calc z ⋆ cBplus φ = z ⋆ (RelB φ ⋆ cBminus φ) := by rw [← h]
      _ = (z ⋆ RelB φ) ⋆ cBminus φ := (mul_assoc_W _ _ _).symm
      _ = (RelB φ ⋆ z) ⋆ cBminus φ := by rw [comm_all_of_mem_Z (RelB_mem_Z φ) z]
      _ = RelB φ ⋆ (z ⋆ cBminus φ) := mul_assoc_W _ _ _

/-! ## §18 — the structural comparison with the inherited A-axis result -/

/-- **COMPARISON (§18), performed only after the independent derivation.**  The
independently derived second-axis sector factors and relative factor coincide, as central
functions of the parameter, with the inherited A-axis ones.  This *identity is derived*,
not conventional: the two derivations used different sector relations (`R ⋆ ψ = ±S ⋆ ψ`
for `A`, `Q ⋆ ψ = ∓S ⋆ ψ` for `B`) and different implementer planes
(`span{1,R}` versus `span{1,Q}`). -/
theorem second_axis_matches_first_axis (φ : ℝ) :
    cBplus φ = cPlusRef φ ∧ cBminus φ = cMinusRef φ ∧ RelB φ = RelRef φ :=
  ⟨rfl, rfl, rfl⟩

end NullSectorTask14
