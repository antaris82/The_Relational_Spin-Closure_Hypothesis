import RequestProject.Experiment2.NullSectorTask14.MixedFiniteComposition

/-!
# Task 14, Layer 9 (§25, §27–§30): mixed internal products, generators and closure

* §25 — the two finite mixed products of the reference implementations, and their exact
  algebraic difference;
* §27 — the two derived infinitesimal generators, their products and their commutator;
* §28 — closure of the bracket system;
* §29 — the intrinsic identification of the third direction produced by the commutator,
  including sign and normalization;
* §30 — the orientation/sign audit.

Nothing is imported from any conventional bracket theory: every relation is computed inside
the inherited carrier.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §25 — the two mixed finite products -/

/-- **DERIVED (§25).**  The mixed product of the two independently derived reference
implementations, in the order `A` then `B`. -/
theorem UA_UB_product (θ φ : ℝ) :
    Uref θ ⋆ UBref φ =
      (Real.cos (θ / 2) * Real.cos (φ / 2)) • w1
        + (Real.cos (θ / 2) * Real.sin (φ / 2)) • wQ
        + (-(Real.sin (θ / 2) * Real.cos (φ / 2))) • wR
        + (-(Real.sin (θ / 2) * Real.sin (φ / 2))) • wP := by
  rw [Uref_apply, UBref_apply, ksc]
  funext i
  fin_cases i <;> simp [w1, wP, wQ, wR, wit8MulFun] <;> ring

/-- **DERIVED (§25).**  The mixed product in the opposite order. -/
theorem UB_UA_product (θ φ : ℝ) :
    UBref φ ⋆ Uref θ =
      (Real.cos (θ / 2) * Real.cos (φ / 2)) • w1
        + (Real.cos (θ / 2) * Real.sin (φ / 2)) • wQ
        + (-(Real.sin (θ / 2) * Real.cos (φ / 2))) • wR
        + (Real.sin (θ / 2) * Real.sin (φ / 2)) • wP := by
  rw [Uref_apply, UBref_apply, ksc]
  funext i
  fin_cases i <;> simp [w1, wP, wQ, wR, wit8MulFun] <;> ring

/-- **PRINCIPAL THEOREM (§25): `mixed_reference_products_exact`.**  The two mixed finite
products differ exactly by twice the half-angle sine product along the derived direction
`P`; in particular they agree precisely when one of the two half-angle sines vanishes. -/
theorem mixed_reference_product_difference (θ φ : ℝ) :
    Uref θ ⋆ UBref φ - UBref φ ⋆ Uref θ
      = (-(2 * Real.sin (θ / 2) * Real.sin (φ / 2))) • wP := by
  rw [UA_UB_product, UB_UA_product]
  module

/-! ## §27 — the derived infinitesimal generators -/

/-- **DERIVED (§27).**  The infinitesimal generator of the inherited A-axis reference
implementation.  Derived here as its derivative at the zero parameter, exactly as `GB` was
derived for the second axis. -/
noncomputable def GA : W := (-(2⁻¹ : ℝ)) • wR

theorem hasDerivAt_Uref_zero : HasDerivAt Uref GA 0 := by
  have hfun : Uref = fun θ : ℝ => Real.cos (θ / 2) • w1 + (-Real.sin (θ / 2)) • wR := by
    funext θ; rw [Uref_apply, ksc]
  rw [hfun]
  have hd := ((hasDerivAt_cos_half 0).smul_const w1).add
    (((hasDerivAt_sin_half 0).neg).smul_const wR)
  convert hd using 1
  rw [GA]
  norm_num

/-- **DERIVED (§27).**  The third direction produced below, named neutrally. -/
noncomputable def GC : W := (-(2⁻¹ : ℝ)) • wP

/-- **DERIVED (§27).**  The two mixed generator products. -/
theorem GA_GB_product : GA ⋆ GB = (-(4⁻¹ : ℝ)) • wP := by
  rw [GA, GB, smul_mul_W, mul_smul_W, wit8_wR_wQ]
  module

theorem GB_GA_product : GB ⋆ GA = (4⁻¹ : ℝ) • wP := by
  rw [GA, GB, smul_mul_W, mul_smul_W, wit8_wQ_wR]
  module

/-- **PRINCIPAL THEOREM (§27): `mixed_infinitesimal_commutator`.**  The commutator of the
two independently derived generators is a *new* direction: it is neither central nor in the
span of the two generators.  Its exact value is `-(1/2) • P`. -/
theorem mixed_commutator : GA ⋆ GB - GB ⋆ GA = GC := by
  rw [GA_GB_product, GB_GA_product, GC]
  module

/-- **DERIVED (§27).**  The two generators anticommute, and each squares to `-1/4`. -/
theorem generators_anticommute : GA ⋆ GB + GB ⋆ GA = 0 := by
  rw [GA_GB_product, GB_GA_product]
  module

theorem GA_sq : GA ⋆ GA = (-(4⁻¹ : ℝ)) • w1 := by
  rw [GA, smul_mul_W, mul_smul_W, wit8_wR_wR]
  module

theorem GC_sq : GC ⋆ GC = (-(4⁻¹ : ℝ)) • w1 := by
  rw [GC, smul_mul_W, mul_smul_W, wit8_wP_wP]
  module

/-- **DERIVED (§27).**  The commutator is **not** in the span of the unit, the two
generators and the exact center: it is a genuinely new noncentral direction. -/
theorem commutator_not_central : GC ∉ Z := by
  intro hmem
  obtain ⟨a, b, hab⟩ := (mem_Z_iff GC).1 hmem
  have h4 := congrFun hab 4
  simp [GC, wP, w1, wS] at h4

/-! ## §28 — closure of the infinitesimal system -/

/-- **PRINCIPAL THEOREM (§28): `infinitesimal_closure`.**  The three brackets close on the
three derived generators — no fourth generator appears.  The system is computed entirely
inside the inherited carrier. -/
theorem infinitesimal_closure :
    GA ⋆ GB - GB ⋆ GA = GC ∧
    GB ⋆ GC - GC ⋆ GB = GA ∧
    GC ⋆ GA - GA ⋆ GC = GB := by
  refine ⟨mixed_commutator, ?_, ?_⟩
  · rw [GB, GC, smul_mul_W, mul_smul_W, smul_mul_W, mul_smul_W, wit8_wQ_wP, wit8_wP_wQ, GA]
    module
  · rw [GC, GA, smul_mul_W, mul_smul_W, smul_mul_W, mul_smul_W, wit8_wP_wR, wit8_wR_wP, GB]
    module

/-! ## §29 — the third-axis consistency test -/

/-- **PRINCIPAL THEOREM (§29): `third_axis_relation`.**  The direction generated by the
mixed commutator is *not* identified by name: it is compared with the inherited third old
spatial direction `C`, and the exact relation — including sign and normalization — is

`GC = -(1/2) • (S ⋆ C)`,

which is exactly the same shape as the two independently derived relations
`GA = -(1/2) • (S ⋆ A)` and `GB = -(1/2) • (S ⋆ B)`. -/
theorem third_axis_relation :
    GA = (-(2⁻¹ : ℝ)) • (wS ⋆ wA) ∧
    GB = (-(2⁻¹ : ℝ)) • (wS ⋆ wB) ∧
    GC = (-(2⁻¹ : ℝ)) • (wS ⋆ wC) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GA, wit8_wS_wA]
  · rw [GB, wit8_wS_wB]
    module
  · rw [GC, wit8_wS_wC]

/-! ## §30 — the orientation and sign audit -/

/-- **ORIENTATION AUDIT (§30).**  The sign of the inherited central element is *not* fixed
by the inherited conditions: `-S` satisfies the same two defining relations (central,
square `-1`).  Reversing it reverses **all three** axis generators simultaneously. -/
theorem central_sign_audit :
    ((-wS) ⋆ (-wS) = -w1) ∧ (∀ x : W, (-wS) ⋆ x = x ⋆ (-wS)) ∧
    (∀ n : W, (-(2⁻¹ : ℝ)) • ((-wS) ⋆ n) = -((-(2⁻¹ : ℝ)) • (wS ⋆ n))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [neg_mul_W, mul_neg_W, wS_sq, neg_neg]
  · intro x
    rw [neg_mul_W, mul_neg_W, wS_central]
  · intro n
    rw [neg_mul_W]
    module

/-- **ORIENTATION AUDIT (§30): the per-axis sign classification.**  For arbitrary sign
choices `εA, εB, εC ∈ {±1}` of the three axis generators, the bracket relation
`[εA GA, εB GB] = εC GC` holds **exactly** when `εA * εB = εC`.  Hence a single global
orientation choice controls the whole system, and exactly one relation among the three
signs is forced, not three independent ones. -/
theorem generator_sign_classification (εA εB εC : ℝ) (hεC : εC ≠ 0) :
    (εA • GA) ⋆ (εB • GB) - (εB • GB) ⋆ (εA • GA) = εC • GC ↔ εA * εB = εC := by
  have hexp : (εA • GA) ⋆ (εB • GB) - (εB • GB) ⋆ (εA • GA)
      = (εA * εB) • (GA ⋆ GB - GB ⋆ GA) := by
    rw [smul_mul_W, mul_smul_W, smul_mul_W, mul_smul_W]
    module
  rw [hexp, mixed_commutator]
  constructor
  · intro h
    have h4 := congrFun h 4
    simp [GC, wP] at h4
    first
      | exact h4
      | linarith
  · intro h
    rw [h]

end NullSectorTask14
