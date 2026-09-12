import RequestProject.Experiment2.NullSectorTask14.CommonFixedLocus

/-!
# Task 14, Layer 20 (§30, §65–§67): rate, isotropy and orientation audits

Three residual freedoms are separated here, none of which is central lift freedom:

* **§65 rate audit** — axis-locally the parameter of each axis family may be rescaled
  freely: `rate_freedom_axis_local`.  This is **RATE-DEPENDENT** data at the level of one
  axis;
* **§66 isotropy audit** — as soon as the axis-generator assignment is required to be the
  *linear* map derived in §31–§32, the per-axis rates are forced to coincide:
  `isotropy_forces_common_rate`.  Verdict: the inherited spatial structure **does** force a
  common normalization;
* **§67, §30 orientation audit** — reversing the inherited central generator reverses every
  axis generator *simultaneously* (`orientation_global_sign`), and a per-axis sign choice
  is nothing but the relabeling `n ↦ -n` (`per_axis_sign_is_axis_reversal`); the sign
  relating the mixed commutator to the third direction is then fixed by
  `generator_sign_classification` (§30).
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §65 — the axis-local rate freedom -/

/-- **DERIVED (§65), `RATE-DEPENDENT`.**  For every nonzero real rate the rescaled family
still satisfies the group law and still implements the corresponding automorphism family.
Axis-locally no rate is singled out. -/
theorem rate_freedom_axis_local {n : Vec3} (hn : IsUnitAxis n) (lam : ℝ) :
    (∀ θ χ : ℝ, Un n (lam * (θ + χ)) = Un n (lam * θ) ⋆ Un n (lam * χ)) ∧
      (∀ (θ : ℝ) (x : W),
        (Un n (lam * θ) ⋆ x) ⋆ Un n (-(lam * θ)) = PhiGen n (lam * θ) x) := by
  refine ⟨fun θ χ => ?_, fun θ x => rfl⟩
  rw [mul_add, Un_group hn]

/-! ## §66 — isotropy forces a common rate -/

theorem sqrt_two_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = 2⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem sqrt_two_inv_ne_zero : (Real.sqrt 2)⁻¹ ≠ 0 := by
  have h : Real.sqrt 2 > 0 := Real.sqrt_pos.2 (by norm_num)
  positivity

/-- **DERIVED (§66).**  The diagonal unit direction between the two basis axes. -/
noncomputable def axAB : Vec3 := ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0)

theorem axAB_unit : IsUnitAxis axAB := by
  have h := sqrt_two_inv_sq
  rw [unitAxis_iff_sumsq]
  simp only [axAB]
  nlinarith [h]

theorem axAB_decomp : axAB = (Real.sqrt 2)⁻¹ • axA + (Real.sqrt 2)⁻¹ • axB := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [axAB, axA, axB]

/-- **PRINCIPAL THEOREM (§66): `isotropy_forces_common_rate`.**  Suppose an axis-generator
assignment is *linear* — as the derived map of §31–§32 is — and that on each unit axis it
is a real multiple of the derived generator direction of that axis.  Then the multiples on
two distinct basis axes and on their diagonal all coincide: the inherited spatial structure
forces **one common rate**.  This is independent of, and additional to, the central lift
freedom. -/
theorem isotropy_forces_common_rate (g : Vec3 →ₗ[ℝ] W) (cA cB cD : ℝ)
    (hA : g axA = cA • Jmap axA) (hB : g axB = cB • Jmap axB)
    (hD : g axAB = cD • Jmap axAB) : cA = cD ∧ cB = cD := by
  have hlin : g axAB = (Real.sqrt 2)⁻¹ • g axA + (Real.sqrt 2)⁻¹ • g axB := by
    rw [axAB_decomp, map_add, map_smul, map_smul]
  have hJ : Jmap axAB = (Real.sqrt 2)⁻¹ • Jmap axA + (Real.sqrt 2)⁻¹ • Jmap axB := by
    rw [axAB_decomp]
    rw [show Jmap ((Real.sqrt 2)⁻¹ • axA + (Real.sqrt 2)⁻¹ • axB)
        = JmapL ((Real.sqrt 2)⁻¹ • axA + (Real.sqrt 2)⁻¹ • axB) from rfl,
      map_add, map_smul, map_smul]
    rfl
  rw [hD, hJ, hA, hB] at hlin
  have h6 := congrFun hlin 6
  have h5 := congrFun hlin 5
  simp [Jmap, axA, axB, wP, wQ, wR] at h6 h5
  have hs := sqrt_two_inv_ne_zero
  exact ⟨mul_left_cancel₀ hs (h6.symm.trans (mul_comm cD _)),
    mul_left_cancel₀ hs (h5.symm.trans (mul_comm cD _))⟩

/-! ## §67, §30 — the orientation audit -/

/-- **DERIVED (§67).**  Reversing the inherited central generator reverses **every** axis
generator simultaneously: one global orientation choice controls all axis signs. -/
theorem orientation_global_sign (n : Vec3) : (-wS) ⋆ spat n = -(Jmap n) := by
  rw [Jmap_eq_central_mul, neg_mul_W]

/-- **DERIVED (§67).**  Reversing the parameter orientation of a single axis is exactly the
relabeling `n ↦ -n`: it is not an independent datum. -/
theorem per_axis_sign_is_axis_reversal (n : Vec3) (θ : ℝ) :
    Jmap (-n) = -(Jmap n) ∧ Un n (-θ) = Un (-n) θ := by
  have hJ : Jmap (-n) = -(Jmap n) := by
    funext i
    fin_cases i <;> simp [Jmap, wP, wQ, wR]
  refine ⟨hJ, ?_⟩
  rw [Un_neg, Un, hJ]
  module

/-- **PRINCIPAL SUMMARY (§30, §65–§67).**  The three audited freedoms and their exact
status:

* axis-local rate: free (`RATE-DEPENDENT`);
* linear axis-generator assignment: forces one common rate (`ISOTROPY`);
* orientation: a single global sign of the inherited central generator flips all axis
  generators at once, and a per-axis sign is a relabeling of the axis; the commutator sign
  relation is then rigid. -/
theorem rate_orientation_audit :
    (∀ (n : Vec3), IsUnitAxis n → ∀ lam θ χ : ℝ,
        Un n (lam * (θ + χ)) = Un n (lam * θ) ⋆ Un n (lam * χ)) ∧
      (∀ (g : Vec3 →ₗ[ℝ] W) (cA cB cD : ℝ), g axA = cA • Jmap axA → g axB = cB • Jmap axB →
        g axAB = cD • Jmap axAB → cA = cD ∧ cB = cD) ∧
      (∀ n : Vec3, (-wS) ⋆ spat n = -(Jmap n)) ∧
      (∀ (εA εB εC : ℝ), εC ≠ 0 →
        ((εA • GA) ⋆ (εB • GB) - (εB • GB) ⋆ (εA • GA) = εC • GC ↔ εA * εB = εC)) :=
  ⟨fun _ hn lam θ χ => (rate_freedom_axis_local hn lam).1 θ χ,
    fun g cA cB cD hA hB hD => isotropy_forces_common_rate g cA cB cD hA hB hD,
    orientation_global_sign,
    fun εA εB εC h => generator_sign_classification εA εB εC h⟩

end NullSectorTask14
