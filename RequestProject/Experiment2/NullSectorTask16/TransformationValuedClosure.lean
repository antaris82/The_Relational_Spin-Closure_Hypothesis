import RequestProject.Experiment2.NullSectorTask16.JointRegularity

/-!
# Task 16, Layer 3 (Work Package 3): global transformation-valued closure

Transformation-valuedness is the intrinsic requirement inherited from Task 15:

```
PhiGen n θ = PhiGen m φ  →  U n θ = U m φ .
```

Combining

* the exact coincidence relation of Work Package 1 — in particular the two exceptional
  identifications `PhiGen n (θ + 2π) = PhiGen n θ` and `PhiGen (-n) θ = PhiGen n (-θ)`;
* the joint regularity of Work Package 2 — which forces the second recovered rate to be a
  *continuous* function of the direction;
* the Task-15 necessary central-rate restrictions — `α ≡ 0`, `β n ∈ ℤ + 1/2`,
  `β (-n) = -β n`;

the global problem closes in the negative:

**Alternative C.  No global jointly regular transformation-valued family exists.**

The obstruction is intrinsic: it is produced by the inherited axis structure alone (a
continuous path of unit directions joining a direction to its reversal), the discreteness
of the surviving central rate, and the antipodal oddness.  Nothing is imported.
-/

namespace NullSectorTask16

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15

/-! ## A continuous path of unit directions joining a direction to its reversal -/

/-- **NEUTRAL DEFINITION.**  The path of unit directions determined by two orthogonal unit
directions. -/
noncomputable def circPath (n m : Vec3) (t : ℝ) : Vec3 :=
  Real.cos t • n + Real.sin t • m

@[simp] theorem circPath_zero (n m : Vec3) : circPath n m 0 = n := by
  simp [circPath]

theorem circPath_pi (n m : Vec3) : circPath n m Real.pi = -n := by
  simp only [circPath, Real.cos_pi, Real.sin_pi, zero_smul, add_zero]
  module

theorem circPath_isUnitAxis {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (hnm : h3 n m = 0) (t : ℝ) : IsUnitAxis (circPath n m t) := by
  have hn' := (isUnitAxis_iff n).1 hn
  have hm' := (isUnitAxis_iff m).1 hm
  have hnm' : n.1 * m.1 + n.2.1 * m.2.1 + n.2.2 * m.2.2 = 0 := by
    simpa [h3, dot3] using hnm
  have hpy := Real.sin_sq_add_cos_sq t
  rw [isUnitAxis_iff]
  simp only [circPath, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (Real.cos t) ^ 2 * hn' + (Real.sin t) ^ 2 * hm'
    + (2 * Real.cos t * Real.sin t) * hnm' + hpy

theorem continuous_circPath (n m : Vec3) : Continuous (circPath n m) := by
  unfold circPath
  refine Continuous.add ?_ ?_
  · exact (Real.continuous_cos.smul continuous_const)
  · exact (Real.continuous_sin.smul continuous_const)

/-! ## A continuous integer-shifted function on an interval does not move -/

/-- **DERIVED.**  A continuous real function on a parameter interval whose values all lie
in a fixed translate of the integers takes the same value at both ends.  Proved from the
intermediate value property alone. -/
theorem eq_of_continuous_int_shift {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ}
    (hint : ∀ t : ℝ, ∃ k : ℤ, g t = k + c) {a b : ℝ} (hab : a ≤ b) : g a = g b := by
  obtain ⟨ka, hka⟩ := hint a
  obtain ⟨kb, hkb⟩ := hint b
  have hnohalf : ∀ (t : ℝ) (k : ℤ), g t ≠ (k : ℝ) + 1 / 2 + c := by
    intro t k hcon
    obtain ⟨j, hj⟩ := hint t
    rw [hj] at hcon
    have : (j : ℝ) = (k : ℝ) + 1 / 2 := by linarith
    have h2 : (2 * j : ℤ) = 2 * k + 1 := by
      have : (2 * (j : ℝ)) = 2 * (k : ℝ) + 1 := by linarith
      exact_mod_cast this
    omega
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exfalso
    have hstep : (ka : ℝ) + 1 ≤ (kb : ℝ) := by exact_mod_cast hlt
    have hmem : (ka : ℝ) + 1 / 2 + c ∈ Set.Icc (g a) (g b) := by
      rw [hka, hkb]; constructor <;> [linarith; linarith]
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc hab hg.continuousOn hmem
    exact hnohalf t ka ht
  · rw [hka, hkb, heq]
  · exfalso
    have hstep : (kb : ℝ) + 1 ≤ (ka : ℝ) := by exact_mod_cast hgt
    have hmem : (kb : ℝ) + 1 / 2 + c ∈ Set.Icc (g b) (g a) := by
      rw [hka, hkb]; constructor <;> [linarith; linarith]
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' hab hg.continuousOn hmem
    exact hnohalf t kb ht

/-! ## Work Package 3 — the global no-go -/

/-- **PRINCIPAL THEOREM (Work Package 3), the obstruction in its sharpest form.**  If a
jointly regular family is transformation-valued, then its second recovered central rate
vanishes in every direction — while the Task-15 restrictions force that rate into
`ℤ + 1/2`.  The two requirements are incompatible. -/
theorem jointlyRegular_transformationValued_beta_zero {U : Vec3 → ℝ → W}
    (hU : IsJointlyRegularFamily U) (hV : IsTransformationValued U) {n : Vec3}
    (hn : IsUnitAxis n) : rateBeta U n = 0 := by
  obtain ⟨m, hm, hnm⟩ := exists_unit_orthogonal hn
  have hβ := jointlyRegular_beta_continuous hU
  set γ : ℝ → Sph := fun t => ⟨circPath n m t, circPath_isUnitAxis hn hm hnm t⟩ with hγ
  have hγc : Continuous γ := (continuous_circPath n m).subtype_mk _
  have hgc : Continuous fun t : ℝ => rateBeta U ((γ t : Sph) : Vec3) := hβ.comp hγc
  have hint : ∀ t : ℝ, ∃ k : ℤ, rateBeta U ((γ t : Sph) : Vec3) = (k : ℝ) + 1 / 2 := by
    intro t
    obtain ⟨k, hk⟩ := autValued_forces_beta_half_odd hU.toRegularFamily hV
      (circPath_isUnitAxis hn hm hnm t)
    exact ⟨k, hk⟩
  have hends := eq_of_continuous_int_shift hgc hint (a := 0) (b := Real.pi)
    (le_of_lt Real.pi_pos)
  have h0 : ((γ 0 : Sph) : Vec3) = n := by rw [hγ]; simp
  have hpi : ((γ Real.pi : Sph) : Vec3) = -n := by rw [hγ]; exact circPath_pi n m
  rw [h0, hpi] at hends
  have hodd := (autValued_antipodal_odd hU.toRegularFamily hV hn).2
  rw [hodd] at hends
  linarith

/-- **PRINCIPAL THEOREM (Work Package 3): alternative C.**  *No* global jointly regular
transformation-valued family exists.  The failure is derived from the inherited axis
structure, the inherited central residual and the joint regularity requirement — no
external construction is used. -/
theorem no_global_jointly_regular_transformationValued :
    ¬ ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U := by
  rintro ⟨U, hU, hV⟩
  have hn : IsUnitAxis ((1, 0, 0) : Vec3) := by simp [IsUnitAxis, h3]
  have hzero := jointlyRegular_transformationValued_beta_zero hU hV hn
  obtain ⟨k, hk⟩ := autValued_forces_beta_half_odd hU.toRegularFamily hV hn
  rw [hzero] at hk
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-- **PRINCIPAL THEOREM (Work Package 3), the same statement in explicit form.**  For every
jointly regular family there is a pair of axis–parameter data representing the *same*
inherited automorphism whose internal representatives differ. -/
theorem jointlyRegular_transformation_valuedness_fails {U : Vec3 → ℝ → W}
    (hU : IsJointlyRegularFamily U) :
    ∃ (n m : Vec3) (θ φ : ℝ), IsUnitAxis n ∧ IsUnitAxis m ∧
      PhiGen n θ = PhiGen m φ ∧ U n θ ≠ U m φ := by
  by_contra hcon
  push_neg at hcon
  have hV : IsTransformationValued U := by
    intro n m θ φ hn hm hP
    exact hcon n m θ φ hn hm hP
  exact no_global_jointly_regular_transformationValued ⟨U, hU, hV⟩

end NullSectorTask16
