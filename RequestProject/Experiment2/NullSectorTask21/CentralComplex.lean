import RequestProject.Experiment2.NullSectorTask21.SectionObstruction

/-!
# Task 21, Package H: the exact central plane and the complex numbers

**IDENTIFICATION / COMPARISON MODULE.**

The intrinsic invertible centre `CUnit` consists of the elements `a·1 + b·S` with
`(a,b) ≠ (0,0)`.  The identification with `ℂˣ` is *not* inferred from `S² = -1`
(negative control 129): the coefficient map itself is constructed, both inverse identities
are proved from coefficient uniqueness, and multiplicativity is proved from the intrinsic
product rule of the central plane.

`IMPORTED STANDARD RESULT`: the complex numbers and their unit group.

`DERIVED IN TASK 21`: every statement below.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-! ## Coefficient uniqueness in the central plane -/

@[simp] theorem zc_coord_zero (a b : ℝ) : zc a b 0 = a := by
  simp [zc, w1, wS]

@[simp] theorem zc_coord_seven (a b : ℝ) : zc a b 7 = b := by
  simp [zc, w1, wS]

/-- **DERIVED.**  Coefficient uniqueness in the exact central plane. -/
theorem zc_inj {a b c d : ℝ} (h : zc a b = zc c d) : a = c ∧ b = d := by
  constructor
  · have h0 := congrFun h 0; simpa using h0
  · have h7 := congrFun h 7; simpa using h7

/-- **DERIVED.**  The intrinsic product rule of the exact central plane. -/
theorem zc_mul (a b c d : ℝ) : zc a b ⋆ zc c d = zc (a * c - b * d) (a * d + b * c) := by
  funext i
  fin_cases i <;> simp [zc, w1, wS]

/-! ## The coefficient map -/

/-- **PACKAGE H (item 76).**  The explicit coefficient map from the carrier to the complex
numbers. -/
def toComplex (x : W) : ℂ := ⟨x 0, x 7⟩

@[simp] theorem toComplex_re (x : W) : (toComplex x).re = x 0 := rfl
@[simp] theorem toComplex_im (x : W) : (toComplex x).im = x 7 := rfl

@[simp] theorem toComplex_zc (a b : ℝ) : toComplex (zc a b) = ⟨a, b⟩ := by
  refine Complex.ext ?_ ?_ <;> simp

/-- **PACKAGE H (item 77).**  The explicit inverse map. -/
noncomputable def ofComplex (z : ℂ) : W := zc z.re z.im

@[simp] theorem ofComplex_toComplex_zc (a b : ℝ) : ofComplex (toComplex (zc a b)) = zc a b := by
  rw [toComplex_zc, ofComplex]

@[simp] theorem toComplex_ofComplex (z : ℂ) : toComplex (ofComplex z) = z := by
  refine Complex.ext ?_ ?_ <;> simp [ofComplex]

theorem ofComplex_mul (z w : ℂ) : ofComplex z ⋆ ofComplex w = ofComplex (z * w) := by
  rw [ofComplex, ofComplex, ofComplex, zc_mul]
  rfl

/-- **PACKAGE H (item 79).**  Multiplicativity on the central plane. -/
theorem toComplex_mul (a b c d : ℝ) :
    toComplex (zc a b ⋆ zc c d) = toComplex (zc a b) * toComplex (zc c d) := by
  rw [zc_mul, toComplex_zc, toComplex_zc, toComplex_zc]
  refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]

theorem toComplex_one : toComplex w1 = 1 := by
  rw [← zc_one_zero, toComplex_zc]
  rfl

theorem toComplex_zero : toComplex (0 : W) = 0 := by
  refine Complex.ext ?_ ?_ <;> simp [toComplex]

theorem toComplex_neg_zc (a b : ℝ) : toComplex (-(zc a b)) = -toComplex (zc a b) := by
  refine Complex.ext ?_ ?_ <;> simp [toComplex]

theorem toComplex_add_zc (a b c d : ℝ) :
    toComplex (zc a b + zc c d) = toComplex (zc a b) + toComplex (zc c d) := by
  refine Complex.ext ?_ ?_ <;> simp [toComplex]

/-- **PACKAGE H (item 80).**  The invertible central elements are exactly the ones with
nonzero complex coefficient. -/
theorem mem_CUnit_iff_toComplex_ne_zero {x : W} :
    x ∈ CUnit ↔ (∃ a b : ℝ, x = zc a b) ∧ toComplex x ≠ 0 := by
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨⟨a, b, rfl⟩, ?_⟩
    rw [toComplex_zc]
    intro h
    exact hab ⟨congrArg Complex.re h, congrArg Complex.im h⟩
  · rintro ⟨⟨a, b, rfl⟩, hne⟩
    refine ⟨a, b, ?_, rfl⟩
    rintro ⟨rfl, rfl⟩
    rw [toComplex_zc] at hne
    exact hne (by refine Complex.ext ?_ ?_ <;> rfl)

theorem toComplex_ne_zero_of_CUnit {x : W} (hx : x ∈ CUnit) : toComplex x ≠ 0 :=
  (mem_CUnit_iff_toComplex_ne_zero.1 hx).2

theorem ofComplex_toComplex_of_CUnit {x : W} (hx : x ∈ CUnit) : ofComplex (toComplex x) = x := by
  obtain ⟨a, b, -, rfl⟩ := hx
  exact ofComplex_toComplex_zc a b

theorem ofComplex_mem_CUnit {z : ℂ} (hz : z ≠ 0) : ofComplex z ∈ CUnit := by
  refine mem_CUnit_iff_toComplex_ne_zero.2 ⟨⟨z.re, z.im, rfl⟩, ?_⟩
  rwa [toComplex_ofComplex]

/-! ## The multiplicative equivalence -/

/-- The packaged invertible central element attached to a nonzero complex number. -/
noncomputable def cwg (z : ℂˣ) : WG where
  val := ofComplex (z : ℂ)
  inv := ofComplex ((z⁻¹ : ℂˣ) : ℂ)
  val_inv := by
    rw [ofComplex_mul]
    rw [show (z : ℂ) * ((z⁻¹ : ℂˣ) : ℂ) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
    rw [ofComplex]
    exact zc_one_zero
  inv_val := by
    rw [ofComplex_mul]
    rw [show ((z⁻¹ : ℂˣ) : ℂ) * (z : ℂ) = 1 by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
    rw [ofComplex]
    exact zc_one_zero

@[simp] theorem cwg_val (z : ℂˣ) : (cwg z).val = ofComplex (z : ℂ) := rfl

theorem cwg_mem_CUnitG (z : ℂˣ) : cwg z ∈ CUnitG :=
  ofComplex_mem_CUnit (Units.ne_zero z)

/-- **PACKAGE H, principal (item 81).**  The intrinsic invertible centre is exactly the
multiplicative group of nonzero complex numbers. -/
noncomputable def cUnitComplexEquiv : CUnitG ≃* ℂˣ where
  toFun u := Units.mk0 (toComplex ((u : WG)).val) (toComplex_ne_zero_of_CUnit u.2)
  invFun z := ⟨cwg z, cwg_mem_CUnitG z⟩
  left_inv u := by
    refine Subtype.ext (WG.ext ?_)
    show ofComplex (toComplex ((u : WG)).val) = ((u : WG)).val
    exact ofComplex_toComplex_of_CUnit u.2
  right_inv z := by
    refine Units.ext ?_
    show toComplex (ofComplex (z : ℂ)) = (z : ℂ)
    exact toComplex_ofComplex _
  map_mul' u v := by
    refine Units.ext ?_
    obtain ⟨a, b, -, hu⟩ := u.2
    obtain ⟨c, d, -, hv⟩ := v.2
    show toComplex (((u : WG)).val ⋆ ((v : WG)).val)
      = toComplex ((u : WG)).val * toComplex ((v : WG)).val
    rw [hu, hv, toComplex_mul]

theorem cUnitComplexEquiv_apply (u : CUnitG) :
    ((cUnitComplexEquiv u : ℂˣ) : ℂ) = toComplex ((u : WG).val) := rfl

theorem cUnitComplexEquiv_symm_val (z : ℂˣ) :
    ((cUnitComplexEquiv.symm z : CUnitG) : WG).val = ofComplex (z : ℂ) := rfl

/-- **PACKAGE H (item 82).**  The topological strengthening at carrier level: the
coefficient map and its inverse are continuous. -/
theorem toComplex_eq (x : W) : toComplex x = (x 0 : ℂ) + (x 7 : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_ <;> simp

theorem continuous_toComplex : Continuous toComplex := by
  have h : toComplex = fun x : W => ((x 0 : ℂ) + (x 7 : ℂ) * Complex.I) := funext toComplex_eq
  rw [h]
  exact ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
    ((Complex.continuous_ofReal.comp (continuous_apply 7)).mul continuous_const))

theorem continuous_ofComplex : Continuous ofComplex := by
  have h : ofComplex = fun z : ℂ => z.re • w1 + z.im • wS := by
    funext z; rw [ofComplex, zc]
  rw [h]
  exact (Complex.continuous_re.smul continuous_const).add
    (Complex.continuous_im.smul continuous_const)

end NullSectorTask21
