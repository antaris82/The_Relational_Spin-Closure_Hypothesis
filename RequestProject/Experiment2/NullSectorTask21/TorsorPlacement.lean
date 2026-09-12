import RequestProject.Experiment2.NullSectorTask21.SignStructures

/-!
# Task 21, Package M: where the half-odd / integer torsor sits

**IDENTIFICATION / COMPARISON MODULE.**

Task 20 proved that the locally exact rate set is an exact torsor over `ℤ`.  Here the rate
data are located inside the identified group structure:

* a single spatial direction is fixed **only as a temporary analysis device** (item 115);
* the corresponding one-parameter subgroup of the reference action is the inherited family
  `θ ↦ Un n θ`;
* the central factor attached to a rate `b` is the inherited `labelBridge b`, and under the
  Package-H identification it is exactly the circle-valued character of weight `b`;
* differences of two local labels are integers exactly because two such characters agree on
  the full-turn parameter iff their weights differ by an integer;
* the Task-20 mod-2 information loss is re-expressed inside the identified central group.

No cohomology object is constructed anywhere (items 123–124).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-! ## The one-parameter subgroups -/

/-- **PACKAGE M (item 116).**  For a fixed direction the reference implementers form a
one-parameter subgroup of the internal core carrier. -/
theorem reference_one_parameter {n : Vec3} (hn : IsUnitAxis n) (θ χ : ℝ) :
    Un n (θ + χ) = Un n θ ⋆ Un n χ := Un_group hn θ χ

/-- **PACKAGE M (item 117).**  The central factor attached to a rate is a one-parameter
subgroup of the exact centre. -/
theorem labelBridge_one_parameter (b θ χ : ℝ) :
    labelBridge b (θ + χ) = labelBridge b θ ⋆ labelBridge b χ := by
  rw [labelBridge_eq, labelBridge_eq, labelBridge_eq, zc_mul,
    show b * (θ + χ) = b * θ + b * χ by ring, Real.cos_add, Real.sin_add]
  congr 1
  ring

/-! ## The exact standard interpretation (items 118–119) -/

/-- **PACKAGE M, principal (items 118–119).**  Under the Package-H identification of the
exact centre with the complex numbers, the central factor of a rate `b` is exactly the
circle-valued character of weight `b`: `θ ↦ exp (i b θ)`.  This is the strongest exact
interpretation available: the local labels are **weights of a one-parameter subgroup of the
identified central circle**, equivalently logarithmic lifts of that circle-valued
character. -/
theorem exp_real_mul_I (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) = ⟨Real.cos t, Real.sin t⟩ := by
  refine Complex.ext ?_ ?_
  · simpa using Complex.exp_ofReal_mul_I_re t
  · simpa using Complex.exp_ofReal_mul_I_im t

theorem toComplex_labelBridge (b θ : ℝ) :
    toComplex (labelBridge b θ) = Complex.exp ((b * θ : ℝ) * Complex.I) := by
  rw [labelBridge_eq, toComplex_zc, exp_real_mul_I]

theorem toComplex_labelBridge_circle (b θ : ℝ) :
    toComplex (labelBridge b θ) = (Circle.exp (b * θ) : ℂ) := by
  rw [toComplex_labelBridge, Circle.coe_exp]

/-! ## Why differences are integers (item 120) -/

/-- **PACKAGE M (item 120).**  Two rates give the same central factor after a full turn
exactly when their weights differ by an integer.  This is the exact reason why differences of
local labels are integers in the identified language. -/
theorem full_turn_eq_iff_int_difference (b b' : ℝ) :
    toComplex (labelBridge b (2 * Real.pi)) = toComplex (labelBridge b' (2 * Real.pi)) ↔
      ∃ k : ℤ, b - b' = (k : ℝ) := by
  rw [toComplex_labelBridge, toComplex_labelBridge, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have h2 : ((b * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
        = (((b' * (2 * Real.pi) : ℝ) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hn]; ring
    have h3 : ((b * (2 * Real.pi) : ℝ) : ℂ)
        = ((b' * (2 * Real.pi) : ℝ) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) :=
      mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : ((b : ℂ) - (b' : ℂ)) * (2 * (Real.pi : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      push_cast at h3 ⊢
      linear_combination h3
    have h5 : (b : ℂ) - (b' : ℂ) = (n : ℂ) :=
      mul_right_cancel₀ (by simpa using hpi) h4
    exact_mod_cast h5
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hb : b = b' + (k : ℝ) := by linarith
    rw [hb]
    push_cast
    ring

/-- **PACKAGE M.**  The inherited exact torsor statement, restated next to its
interpretation. -/
theorem halfOdd_differences_are_integers {b b' : ℝ} (hb : b ∈ HalfOddSet)
    (hb' : b' ∈ HalfOddSet) : ∃ k : ℤ, b - b' = (k : ℝ) := by
  obtain ⟨k, hk⟩ := hb
  obtain ⟨l, hl⟩ := hb'
  refine ⟨k - l, ?_⟩
  rw [hk, hl]
  push_cast
  ring

/-! ## What the full turn remembers and what it forgets (items 121–122) -/

theorem toComplex_neg_w1 : toComplex (-w1 : W) = -1 := by
  rw [← zc_neg_one_zero, toComplex_zc]
  refine Complex.ext ?_ ?_ <;> simp

/-- **PACKAGE M (items 121–122).**  Inside the identified central group the full-turn value
of a half-odd rate is exactly `-1`, for *every* half-odd rate: the full turn remembers the
half-odd/integer alternative and forgets the integer offset.  Two distinct half-odd rates,
distinguishable at other parameters, are indistinguishable after a full turn. -/
theorem full_turn_remembers_only_parity :
    (∀ b : ℝ, b ∈ HalfOddSet → toComplex (labelBridge b (2 * Real.pi)) = -1) ∧
      (∀ b : ℝ, (∃ k : ℤ, b = (k : ℝ)) → toComplex (labelBridge b (2 * Real.pi)) = 1) ∧
      (∃ b b' : ℝ, b ∈ HalfOddSet ∧ b' ∈ HalfOddSet ∧ b ≠ b' ∧
        toComplex (labelBridge b (2 * Real.pi)) = toComplex (labelBridge b' (2 * Real.pi)) ∧
        ∃ θ : ℝ, toComplex (labelBridge b θ) ≠ toComplex (labelBridge b' θ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rw [labelBridge_full_turn hb, toComplex_neg_w1]
  · rintro b ⟨k, rfl⟩
    rw [toComplex_labelBridge]
    have h : ((k : ℝ) * (2 * Real.pi) : ℝ) = (k : ℝ) * (2 * Real.pi) := rfl
    rw [h]
    have : (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · refine ⟨1 / 2, 5 / 2, ⟨0, by norm_num⟩, ⟨2, by norm_num⟩, by norm_num, ?_, ?_⟩
    · rw [(full_turn_eq_iff_int_difference (1 / 2) (5 / 2)).2 ⟨-2, by norm_num⟩]
    · refine ⟨Real.pi / 2, ?_⟩
      rw [toComplex_labelBridge, toComplex_labelBridge]
      intro hcon
      have hre := congrArg Complex.re hcon
      rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at hre
      have e1' : (1 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 := by ring
      have e2' : (5 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 + Real.pi := by ring
      rw [e1', e2', Real.cos_add_pi, Real.cos_pi_div_four] at hre
      have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.2 (by norm_num)
      linarith

end NullSectorTask21
