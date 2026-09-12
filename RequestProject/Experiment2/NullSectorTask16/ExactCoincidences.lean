import RequestProject.Experiment2.NullSectorTask16.SafeBase

/-!
# Task 16, Layer 1 (Work Package 1): exact transformation coincidences

The question of this layer is purely internal to the inherited data: *when do two
axis–parameter pairs represent the same inherited visible automorphism?*

The answer is complete (necessary **and** sufficient) and intrinsic:

```
PhiGen n θ = PhiGen m φ
  ↔  Un n θ = Un m φ  ∨  Un n θ = -(Un m φ)
  ↔  (cos (θ/2) =  cos (φ/2) ∧ sin (θ/2) • n =  sin (φ/2) • m)
   ∨ (cos (θ/2) = -cos (φ/2) ∧ sin (θ/2) • n = -(sin (φ/2) • m)) .
```

The whole list of exceptional cases demanded by the task is then *derived* from this one
theorem and not postulated:

* parameter periodicity (`coincidence_add_two_pi`, `coincidence_same_axis_iff`);
* axis reversal (`coincidence_neg_axis`);
* zero / identity transformations (`coincidence_id_iff`);
* the finite-angle degeneracy at the half turn, where the axis is *not* determined
  (`coincidence_axis_undetermined_at_zero_angle`) versus the generic case, where it is
  determined up to reversal (`coincidence_axis_determined`).

Nothing in this layer solves the arbitrary spatial word problem: only the exact
equivalence relation carried by the existing axis–parameter representation is classified.
-/

namespace NullSectorTask16

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15

/-! ## The sign-normalized form of a coincidence -/

/-- **NEUTRAL DEFINITION.**  The two axis–parameter pairs carry *proportional* reference
implementations with a sign factor `e ∈ {1, -1}`.  This is the exact intrinsic datum that
Work Package 1 classifies. -/
def SignRelated (n m : Vec3) (θ φ : ℝ) : Prop :=
  ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ Un n θ = e • Un m φ

theorem SignRelated.refl (n : Vec3) (θ : ℝ) : SignRelated n n θ θ :=
  ⟨1, Or.inl rfl, by rw [one_smul]⟩

/-- **DERIVED.**  A sign relation between the reference implementations propagates to the
reflected parameters. -/
theorem Un_neg_of_signRelated {n m : Vec3} {θ φ : ℝ} {e : ℝ} (he : e = 1 ∨ e = -1)
    (h : Un n θ = e • Un m φ) : Un n (-θ) = e • Un m (-φ) := by
  have hc : Real.cos (θ / 2) = e * Real.cos (φ / 2) := by
    have := congrFun h 0
    simpa using this
  rw [Un_neg_eq, Un_neg_eq, h, hc]
  rcases he with rfl | rfl <;> module

/-- **DERIVED.**  Sign-related pairs implement the same inherited automorphism.  (The
sufficiency half of Work Package 1.) -/
theorem phiGen_eq_of_signRelated {n m : Vec3} {θ φ : ℝ} (h : SignRelated n m θ φ) :
    PhiGen n θ = PhiGen m φ := by
  obtain ⟨e, he, hUn⟩ := h
  have hneg := Un_neg_of_signRelated he hUn
  refine LinearMap.ext (fun x => ?_)
  show (Un n θ ⋆ x) ⋆ Un n (-θ) = (Un m φ ⋆ x) ⋆ Un m (-φ)
  rw [hUn, hneg]
  simp only [smul_mul_W, mul_smul_W, smul_smul]
  have : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  rw [this, one_smul]

/-! ## Necessity -/

/-- **DERIVED.**  A central multiple of a reference implementation which is again a
reference implementation has a *real* central factor of square one.  The two coefficient
equations are read off from the inherited coordinates. -/
theorem central_factor_normalization {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    {θ φ a b : ℝ} (h : Un n θ = zc a b ⋆ Un m φ) :
    b = 0 ∧ a ^ 2 = 1 ∧ Real.cos (θ / 2) = a * Real.cos (φ / 2) ∧
      Real.sin (θ / 2) • n = (a * Real.sin (φ / 2)) • m := by
  have hm' := (isUnitAxis_iff m).1 hm
  have hn' := (isUnitAxis_iff n).1 hn
  have c7 : (0 : ℝ) = b * Real.cos (φ / 2) := by
    have := congrFun h 7; simpa using this
  have c1 : (0 : ℝ) = b * Real.sin (φ / 2) * m.1 := by
    have := congrFun h 1; rw [zc_mul_Un_coord_1] at this; simpa using this
  have c2 : (0 : ℝ) = b * Real.sin (φ / 2) * m.2.1 := by
    have := congrFun h 2; rw [zc_mul_Un_coord_2] at this; simpa using this
  have c3 : (0 : ℝ) = b * Real.sin (φ / 2) * m.2.2 := by
    have := congrFun h 3; rw [zc_mul_Un_coord_3] at this; simpa using this
  have c0 : Real.cos (θ / 2) = a * Real.cos (φ / 2) := by
    have := congrFun h 0; simpa using this
  have c4 : -(Real.sin (θ / 2) * n.2.2) = -(a * Real.sin (φ / 2)) * m.2.2 := by
    have := congrFun h 4; rw [zc_mul_Un_coord_4] at this; simpa using this
  have c5 : Real.sin (θ / 2) * n.2.1 = a * Real.sin (φ / 2) * m.2.1 := by
    have := congrFun h 5; rw [zc_mul_Un_coord_5] at this; simpa using this
  have c6 : -(Real.sin (θ / 2) * n.1) = -(a * Real.sin (φ / 2)) * m.1 := by
    have := congrFun h 6; rw [zc_mul_Un_coord_6] at this; simpa using this
  have hpyφ := Real.sin_sq_add_cos_sq (φ / 2)
  have hpyθ := Real.sin_sq_add_cos_sq (θ / 2)
  have hbs : b * Real.sin (φ / 2) = 0 := by
    have hsq0 : (b * Real.sin (φ / 2)) ^ 2 = 0 := by
      linear_combination (-((b * Real.sin (φ / 2)) ^ 2)) * hm'
        - (b * Real.sin (φ / 2) * m.1) * c1 - (b * Real.sin (φ / 2) * m.2.1) * c2
        - (b * Real.sin (φ / 2) * m.2.2) * c3
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq0
  have hbc : b * Real.cos (φ / 2) = 0 := c7.symm
  have hb : b = 0 := by
    have hsq0 : b ^ 2 = 0 := by
      linear_combination (-(b ^ 2)) * hpyφ + (b * Real.sin (φ / 2)) * hbs
        + (b * Real.cos (φ / 2)) * hbc
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq0
  have hsm : Real.sin (θ / 2) • n = (a * Real.sin (φ / 2)) • m := by
    have h1 : Real.sin (θ / 2) * n.1 = a * Real.sin (φ / 2) * m.1 := by linarith
    have h3' : Real.sin (θ / 2) * n.2.2 = a * Real.sin (φ / 2) * m.2.2 := by linarith
    exact Prod.ext h1 (Prod.ext c5 h3')
  have hsq := unit_smul_sq hn hm hsm
  refine ⟨hb, ?_, c0, hsm⟩
  linear_combination (-hsq) - (Real.cos (θ / 2) + a * Real.cos (φ / 2)) * c0 + hpyθ
    - a ^ 2 * hpyφ

/-- **PRINCIPAL THEOREM (Work Package 1): `coincidence_iff`.**  Two axis–parameter pairs
represent the same inherited visible automorphism **exactly** when their reference
implementations agree up to sign.  Necessary and sufficient, with no side condition beyond
unitarity of the two directions. -/
theorem coincidence_iff {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m) (θ φ : ℝ) :
    PhiGen n θ = PhiGen m φ ↔ SignRelated n m θ φ := by
  constructor
  · intro hP
    have hu : Implements (Un n θ) (Un n (-θ)) (PhiGen n θ) := Un_implements hn θ
    have hv : Implements (Un m φ) (Un m (-φ)) (PhiGen n θ) := by
      rw [hP]; exact Un_implements hm φ
    obtain ⟨z, hzZ, hz⟩ := implements_defect_factor hu hv
    obtain ⟨a, b, hab⟩ := (mem_Z_iff z).1 hzZ
    rw [hab] at hz
    have hz' : Un n θ = zc a b ⋆ Un m φ := hz
    obtain ⟨-, ha, -, -⟩ := central_factor_normalization hn hm hz'
    refine ⟨a, ?_, ?_⟩
    · rcases mul_eq_zero.1 (by nlinarith [ha] : (a - 1) * (a + 1) = 0) with h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · obtain ⟨hb, -, -, -⟩ := central_factor_normalization hn hm hz'
      rw [hz', hb]
      funext i
      have : zc a 0 = a • w1 := by funext j; fin_cases j <;> simp [zc, w1, wS]
      rw [this, smul_mul_W, one_mul_W]
  · exact phiGen_eq_of_signRelated

/-- **PRINCIPAL THEOREM (Work Package 1), coordinate form.**  The same classification,
written out entirely in the inherited real data. -/
theorem coincidence_iff_coords {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (θ φ : ℝ) :
    PhiGen n θ = PhiGen m φ ↔
      (Real.cos (θ / 2) = Real.cos (φ / 2) ∧ Real.sin (θ / 2) • n = Real.sin (φ / 2) • m) ∨
      (Real.cos (θ / 2) = -Real.cos (φ / 2) ∧
        Real.sin (θ / 2) • n = -(Real.sin (φ / 2) • m)) := by
  rw [coincidence_iff hn hm]
  constructor
  · rintro ⟨e, he, hUn⟩
    have hc : Real.cos (θ / 2) = e * Real.cos (φ / 2) := by
      have := congrFun hUn 0; simpa using this
    have h6 : -(Real.sin (θ / 2) * n.1) = e * -(Real.sin (φ / 2) * m.1) := by
      have := congrFun hUn 6; simpa using this
    have h5 : Real.sin (θ / 2) * n.2.1 = e * (Real.sin (φ / 2) * m.2.1) := by
      have := congrFun hUn 5; simpa using this
    have h4 : -(Real.sin (θ / 2) * n.2.2) = e * -(Real.sin (φ / 2) * m.2.2) := by
      have := congrFun hUn 4; simpa using this
    have hsm : Real.sin (θ / 2) • n = (e * Real.sin (φ / 2)) • m :=
      Prod.ext (by simpa using by linarith) (Prod.ext (by simpa using by linarith)
        (by simpa using by linarith))
    rcases he with rfl | rfl
    · exact Or.inl ⟨by linarith, by simpa using hsm⟩
    · refine Or.inr ⟨by linarith, ?_⟩
      rw [hsm]
      module
  · rintro (⟨hc, hs⟩ | ⟨hc, hs⟩)
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_smul, Un, Un, hc]
      congr 1
      have : Real.sin (θ / 2) • n = Real.sin (φ / 2) • m := hs
      rw [← Jmap_linear.2, ← Jmap_linear.2, this]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have hs' : Real.sin (θ / 2) • n = (-Real.sin (φ / 2)) • m := by
        rw [hs]; module
      rw [Un, Un, hc, ← Jmap_linear.2 (Real.sin (θ / 2)) n, hs', Jmap_linear.2]
      module

/-! ## The exceptional cases, all derived -/

/-- **DERIVED.**  A full turn of the parameter reverses the reference implementation. -/
theorem Un_add_two_pi (n : Vec3) (θ : ℝ) :
    Un n (θ + 2 * Real.pi) = -(Un n θ) := by
  have hc : Real.cos ((θ + 2 * Real.pi) / 2) = -Real.cos (θ / 2) := by
    rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.cos_add_pi]
  have hs : Real.sin ((θ + 2 * Real.pi) / 2) = -Real.sin (θ / 2) := by
    rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.sin_add_pi]
  rw [Un, Un, hc, hs]
  module

/-- **DERIVED (parameter periodicity).**  The inherited automorphism family has parameter
period `2π`. -/
theorem coincidence_add_two_pi (n : Vec3) (θ : ℝ) :
    PhiGen n (θ + 2 * Real.pi) = PhiGen n θ :=
  phiGen_eq_of_signRelated ⟨-1, Or.inr rfl, by rw [Un_add_two_pi]; module⟩

/-- **DERIVED (axis reversal).**  Reversing the direction is the same as reversing the
parameter.  (Inherited from Task 15; restated here as one of the exceptional cases of the
coincidence relation.) -/
theorem coincidence_neg_axis (n : Vec3) (θ : ℝ) : PhiGen (-n) θ = PhiGen n (-θ) :=
  PhiGen_neg_axis n θ

/-- **DERIVED (identity / zero transformations).**  The inherited automorphism of an
axis–parameter pair is the identity exactly at the integer multiples of `2π`. -/
theorem coincidence_id_iff {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    PhiGen n θ = LinearMap.id ↔ ∃ k : ℤ, θ = 2 * Real.pi * k := by
  have hid : (LinearMap.id : W →ₗ[ℝ] W) = PhiGen n 0 := by
    refine LinearMap.ext (fun x => ?_)
    show x = (Un n 0 ⋆ x) ⋆ Un n (-0)
    rw [neg_zero, Un_zero, one_mul_W, mul_one_W]
  rw [hid, coincidence_iff_coords hn hn]
  constructor
  · intro h
    have hs0 : Real.sin (θ / 2) = 0 := by
      have hz : Real.sin (θ / 2) • n = 0 := by
        rcases h with ⟨-, hs⟩ | ⟨-, hs⟩ <;>
          simpa using hs
      exact smul_unit_eq_zero hn hz
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hs0
    exact ⟨k, by linarith [hk]⟩
  · rintro ⟨k, rfl⟩
    have hs0 : Real.sin (2 * Real.pi * (k : ℝ) / 2) = 0 :=
      Real.sin_eq_zero_iff.2 ⟨k, by ring⟩
    have hpy := Real.sin_sq_add_cos_sq (2 * Real.pi * (k : ℝ) / 2)
    have hc2 : Real.cos (2 * Real.pi * (k : ℝ) / 2) ^ 2 = 1 := by nlinarith [hs0, hpy]
    rcases mul_eq_zero.1 (by nlinarith [hc2] :
        (Real.cos (2 * Real.pi * (k : ℝ) / 2) - 1) *
          (Real.cos (2 * Real.pi * (k : ℝ) / 2) + 1) = 0) with h' | h'
    · exact Or.inl ⟨by simp; linarith, by rw [hs0]; simp⟩
    · exact Or.inr ⟨by simp; linarith, by rw [hs0]; simp⟩

/-- **DERIVED (same-axis parameter periodicity).**  For a fixed direction, two parameters
give the same inherited automorphism exactly when they differ by an integer multiple of
`2π`. -/
theorem coincidence_same_axis_iff {n : Vec3} (hn : IsUnitAxis n) (θ φ : ℝ) :
    PhiGen n θ = PhiGen n φ ↔ ∃ k : ℤ, θ - φ = 2 * Real.pi * k := by
  rw [coincidence_iff_coords hn hn]
  have hpy := Real.sin_sq_add_cos_sq (φ / 2)
  constructor
  · rintro (⟨hc, hs⟩ | ⟨hc, hs⟩)
    · have hs' : Real.sin (θ / 2) = Real.sin (φ / 2) := smul_unit_inj hn hs
      have hcos : Real.cos (θ / 2 - φ / 2) = 1 := by
        rw [Real.cos_sub, hc, hs']; linarith [hpy]
      obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 hcos
      exact ⟨2 * j, by push_cast; linarith [hj]⟩
    · have hs' : Real.sin (θ / 2) = -Real.sin (φ / 2) := by
        refine smul_unit_inj hn ?_
        rw [hs]; module
      have hcos : Real.cos (θ / 2 - φ / 2 - Real.pi) = 1 := by
        rw [show θ / 2 - φ / 2 - Real.pi = (θ / 2 - φ / 2) + -Real.pi by ring,
          Real.cos_add, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi,
          Real.cos_sub, Real.sin_sub, hc, hs']
        linarith [hpy]
      obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 hcos
      exact ⟨2 * j + 1, by push_cast; linarith [hj]⟩
  · rintro ⟨k, hk⟩
    have hθ : θ / 2 = φ / 2 + Real.pi * k := by linarith [hk]
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      have hjr : (k : ℝ) = 2 * (j : ℝ) := by rw [hj]; push_cast; ring
      constructor
      · rw [hθ, hjr, show Real.pi * (2 * (j : ℝ)) = (j : ℝ) * (2 * Real.pi) by ring,
          Real.cos_add_int_mul_two_pi]
      · rw [hθ, hjr, show Real.pi * (2 * (j : ℝ)) = (j : ℝ) * (2 * Real.pi) by ring,
          Real.sin_add_int_mul_two_pi]
    · right
      have hjr : (k : ℝ) = 2 * (j : ℝ) + 1 := by rw [hj]; push_cast; ring
      have hrw : θ / 2 = (φ / 2 + Real.pi) + (j : ℝ) * (2 * Real.pi) := by
        rw [hθ, hjr]; ring
      constructor
      · rw [hrw, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
      · rw [hrw, Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
        module


/-- **DERIVED (generic case).**  Outside the degenerate parameters the direction is
determined up to reversal. -/
theorem coincidence_axis_determined {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    {θ φ : ℝ} (hθ : Real.sin (θ / 2) ≠ 0) (h : PhiGen n θ = PhiGen m φ) :
    n = m ∨ n = -m := by
  obtain ⟨e, he, hUn⟩ := (coincidence_iff hn hm θ φ).1 h
  have h6 : -(Real.sin (θ / 2) * n.1) = e * -(Real.sin (φ / 2) * m.1) := by
    have := congrFun hUn 6; simpa using this
  have h5 : Real.sin (θ / 2) * n.2.1 = e * (Real.sin (φ / 2) * m.2.1) := by
    have := congrFun hUn 5; simpa using this
  have h4 : -(Real.sin (θ / 2) * n.2.2) = e * -(Real.sin (φ / 2) * m.2.2) := by
    have := congrFun hUn 4; simpa using this
  have hsm : Real.sin (θ / 2) • n = (e * Real.sin (φ / 2)) • m :=
    Prod.ext (by simpa using by linarith) (Prod.ext (by simpa using by linarith)
      (by simpa using by linarith))
  have hsq := unit_smul_sq hn hm hsm
  have hne : e * Real.sin (φ / 2) ≠ 0 := by
    intro h0
    apply hθ
    nlinarith [hsq, h0]
  have hquot := unit_eq_of_smul hθ hsm
  have hratio : (e * Real.sin (φ / 2) / Real.sin (θ / 2)) ^ 2 = 1 := by
    field_simp
    nlinarith [hsq]
  rcases mul_eq_zero.1 (by nlinarith [hratio] :
      (e * Real.sin (φ / 2) / Real.sin (θ / 2) - 1) *
        (e * Real.sin (φ / 2) / Real.sin (θ / 2) + 1) = 0) with h' | h'
  · left
    rw [hquot, show e * Real.sin (φ / 2) / Real.sin (θ / 2) = 1 by linarith, one_smul]
  · right
    rw [hquot, show e * Real.sin (φ / 2) / Real.sin (θ / 2) = -1 by linarith]
    module

/-- **DERIVED (finite-angle degeneracy).**  At the degenerate parameters the direction is
*not* determined: every unit direction represents the same inherited automorphism.  This
is the exceptional case that the classification has to contain. -/
theorem coincidence_axis_undetermined_at_zero_angle {n m : Vec3} (hn : IsUnitAxis n)
    (hm : IsUnitAxis m) (k l : ℤ) :
    PhiGen n (2 * Real.pi * k) = PhiGen m (2 * Real.pi * l) := by
  rw [(coincidence_id_iff hn (2 * Real.pi * k)).2 ⟨k, rfl⟩,
    (coincidence_id_iff hm (2 * Real.pi * l)).2 ⟨l, rfl⟩]

end NullSectorTask16
