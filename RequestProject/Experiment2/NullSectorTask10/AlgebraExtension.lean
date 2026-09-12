import RequestProject.Experiment2.NullSectorTask10.OldAxialRotation

/-!
# Task 10, Layer 3: does the old axial rotation extend to the whole algebra?

The question of §8 of the task is asked for an **entirely unknown** real-linear
map `Φ : W →ₗ[ℝ] W` subject only to

* `Φ (ι₃ X) = ι₃ (rot θ X)` for every old vector `X`,
* `Φ (x ⋆ y) = Φ x ⋆ Φ y`,
* `Φ 1 = 1`.

No value on `P, Q, R, S` is prescribed.  The order of this module is

1. the forced values (a derivation, from the hypotheses only);
2. uniqueness of the extension;
3. only afterwards, an explicit existence witness;
4. the one-parameter group law and the `2π` return.

`Real.sin_sq_add_cos_sq`, `Real.cos_add`, `Real.sin_add`, `Real.cos_two_pi`,
`Real.sin_two_pi` are the only imported analytic facts.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## The extension problem -/

/-- **THE EXTENSION PROBLEM.**  A unital multiplicative real-linear map of the
carrier extending the old axial rotation of angle `θ`. -/
structure IsAxialExtension (θ : ℝ) (Φ : W →ₗ[ℝ] W) : Prop where
  /-- The unit is preserved. -/
  unital : Φ w1 = w1
  /-- The map is multiplicative for the inherited product. -/
  mul : ∀ x y : W, Φ (x ⋆ y) = Φ x ⋆ Φ y
  /-- On embedded old vectors the map is the old axial rotation. -/
  old : ∀ X : Vec4, Φ (iota3 X) = iota3 (rot θ X)

/-! ## A transverse product identity used in the derivation -/

/-- The product of the two rotated transverse generators.  The Pythagorean
identity is the only analytic input. -/
theorem transverse_product (θ : ℝ) :
    (Real.cos θ • wB + Real.sin θ • wC) ⋆ ((- Real.sin θ) • wB + Real.cos θ • wC)
      = wR := by
  have hpy := Real.sin_sq_add_cos_sq θ
  funext i
  fin_cases i <;> simp [wB, wC, wR] <;> nlinarith [hpy]

/-! ## Step 1 — the forced values (derivation) -/

section Forced

variable {θ : ℝ} {Φ : W →ₗ[ℝ] W} (h : IsAxialExtension θ Φ)
include h

theorem forced_wA : Φ wA = wA := by
  have := h.old dirA
  rwa [iota3_dirA, rot_dirA, iota3_dirA] at this

theorem forced_wB : Φ wB = Real.cos θ • wB + Real.sin θ • wC := by
  have := h.old dirB
  rw [iota3_dirB, rot_dirB, map_add, map_smul, map_smul, iota3_dirB,
    iota3_dirC] at this
  exact this

theorem forced_wC : Φ wC = (- Real.sin θ) • wB + Real.cos θ • wC := by
  have := h.old dirC
  rw [iota3_dirC, rot_dirC, map_add, map_smul, map_smul, iota3_dirB,
    iota3_dirC] at this
  exact this

/-- **FORCED, NOT PRESCRIBED.**  The value on `P = A ⋆ B` follows from
multiplicativity. -/
theorem forced_wP : Φ wP = Real.cos θ • wP + Real.sin θ • wQ := by
  have hP : wP = wA ⋆ wB := (wit8_wA_wB).symm
  rw [hP, h.mul, forced_wA h, forced_wB h]
  rw [mul_add_W, mul_smul_W, mul_smul_W, wit8_wA_wB, wit8_wA_wC]

/-- **FORCED.**  The value on `Q = A ⋆ C`. -/
theorem forced_wQ : Φ wQ = (- Real.sin θ) • wP + Real.cos θ • wQ := by
  have hQ : wQ = wA ⋆ wC := (wit8_wA_wC).symm
  rw [hQ, h.mul, forced_wA h, forced_wC h]
  rw [mul_add_W, mul_smul_W, mul_smul_W, wit8_wA_wB, wit8_wA_wC]

/-- **FORCED.**  The value on `R = B ⋆ C`: the transverse product channel is
*fixed*, the Pythagorean identity being the only analytic input. -/
theorem forced_wR : Φ wR = wR := by
  have hR : wR = wB ⋆ wC := (wit8_wB_wC).symm
  conv_lhs => rw [hR]
  rw [h.mul, forced_wB h, forced_wC h, transverse_product]

/-- **FORCED.**  The value on the central element `S = A ⋆ R`. -/
theorem forced_wS : Φ wS = wS := by
  have hS : wS = wA ⋆ wR := (wit8_wA_wR).symm
  rw [hS, h.mul, forced_wA h, forced_wR h, wit8_wA_wR]

end Forced

/-! ## Step 2 — uniqueness -/

/-- **UNIQUENESS OF THE ALGEBRA EXTENSION.**  Two extensions of the same old
axial rotation coincide, because the carrier is generated multiplicatively by
`1, A, B, C`. -/
theorem axialExtension_unique {θ : ℝ} {Φ Ψ : W →ₗ[ℝ] W}
    (hΦ : IsAxialExtension θ Φ) (hΨ : IsAxialExtension θ Ψ) : Φ = Ψ :=
  linMap_ext
    (by rw [hΦ.unital, hΨ.unital])
    (by rw [forced_wA hΦ, forced_wA hΨ])
    (by rw [forced_wB hΦ, forced_wB hΨ])
    (by rw [forced_wC hΦ, forced_wC hΨ])
    (by rw [forced_wP hΦ, forced_wP hΨ])
    (by rw [forced_wQ hΦ, forced_wQ hΨ])
    (by rw [forced_wR hΦ, forced_wR hΨ])
    (by rw [forced_wS hΦ, forced_wS hΨ])

/-! ## Step 3 — the explicit existence witness -/

/-- The coordinate description of the candidate extension.  Its coordinates are
exactly the values forced in Step 1. -/
noncomputable def PhiFun (θ : ℝ) (x : W) : W :=
  ![x 0, x 1,
    Real.cos θ * x 2 - Real.sin θ * x 3,
    Real.sin θ * x 2 + Real.cos θ * x 3,
    Real.cos θ * x 4 - Real.sin θ * x 5,
    Real.sin θ * x 4 + Real.cos θ * x 5,
    x 6, x 7]

/-- **THE CANDIDATE EXTENSION**, as a real-linear map. -/
noncomputable def Phi (θ : ℝ) : W →ₗ[ℝ] W where
  toFun := PhiFun θ
  map_add' := by intro x y; funext i; fin_cases i <;> simp [PhiFun] <;> ring
  map_smul' := by intro c x; funext i; fin_cases i <;> simp [PhiFun] <;> ring

theorem Phi_apply (θ : ℝ) (x : W) : Phi θ x = PhiFun θ x := rfl

@[simp] theorem Phi_coord_0 (θ : ℝ) (x : W) : Phi θ x 0 = x 0 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_1 (θ : ℝ) (x : W) : Phi θ x 1 = x 1 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_2 (θ : ℝ) (x : W) :
    Phi θ x 2 = Real.cos θ * x 2 - Real.sin θ * x 3 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_3 (θ : ℝ) (x : W) :
    Phi θ x 3 = Real.sin θ * x 2 + Real.cos θ * x 3 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_4 (θ : ℝ) (x : W) :
    Phi θ x 4 = Real.cos θ * x 4 - Real.sin θ * x 5 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_5 (θ : ℝ) (x : W) :
    Phi θ x 5 = Real.sin θ * x 4 + Real.cos θ * x 5 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_6 (θ : ℝ) (x : W) : Phi θ x 6 = x 6 := by simp [Phi, PhiFun]
@[simp] theorem Phi_coord_7 (θ : ℝ) (x : W) : Phi θ x 7 = x 7 := by simp [Phi, PhiFun]

/-! ### Multiplicativity of the candidate -/

/-- **THE CANDIDATE IS MULTIPLICATIVE.**  Direct verification in the derived
coordinates; the Pythagorean identity is the only analytic input. -/
theorem Phi_mul (θ : ℝ) (x y : W) : Phi θ (x ⋆ y) = Phi θ x ⋆ Phi θ y := by
  have hpy := Real.sin_sq_add_cos_sq θ
  have h0 : Phi θ (x ⋆ y) 0 = (Phi θ x ⋆ Phi θ y) 0 := by
    simp only [Phi_coord_0, wit8Mul_coord_0, Phi_coord_1, Phi_coord_2,
      Phi_coord_3, Phi_coord_4, Phi_coord_5, Phi_coord_6, Phi_coord_7]
    linear_combination (-(x 2 * y 2) - x 3 * y 3 + x 4 * y 4 + x 5 * y 5) * hpy
  have h1 : Phi θ (x ⋆ y) 1 = (Phi θ x ⋆ Phi θ y) 1 := by
    simp only [Phi_coord_1, wit8Mul_coord_1, Phi_coord_0, Phi_coord_2,
      Phi_coord_3, Phi_coord_4, Phi_coord_5, Phi_coord_6, Phi_coord_7]
    linear_combination (x 2 * y 4 + x 3 * y 5 - x 4 * y 2 - x 5 * y 3) * hpy
  have h2 : Phi θ (x ⋆ y) 2 = (Phi θ x ⋆ Phi θ y) 2 := by
    simp only [Phi_coord_2, wit8Mul_coord_2, wit8Mul_coord_3, Phi_coord_0,
      Phi_coord_1, Phi_coord_3, Phi_coord_4, Phi_coord_5, Phi_coord_6,
      Phi_coord_7]
    ring
  have h3 : Phi θ (x ⋆ y) 3 = (Phi θ x ⋆ Phi θ y) 3 := by
    simp only [Phi_coord_3, wit8Mul_coord_2, wit8Mul_coord_3, Phi_coord_0,
      Phi_coord_1, Phi_coord_2, Phi_coord_4, Phi_coord_5, Phi_coord_6,
      Phi_coord_7]
    ring
  have h4 : Phi θ (x ⋆ y) 4 = (Phi θ x ⋆ Phi θ y) 4 := by
    simp only [Phi_coord_4, wit8Mul_coord_4, wit8Mul_coord_5, Phi_coord_0,
      Phi_coord_1, Phi_coord_2, Phi_coord_3, Phi_coord_5, Phi_coord_6,
      Phi_coord_7]
    ring
  have h5 : Phi θ (x ⋆ y) 5 = (Phi θ x ⋆ Phi θ y) 5 := by
    simp only [Phi_coord_5, wit8Mul_coord_4, wit8Mul_coord_5, Phi_coord_0,
      Phi_coord_1, Phi_coord_2, Phi_coord_3, Phi_coord_4, Phi_coord_6,
      Phi_coord_7]
    ring
  have h6 : Phi θ (x ⋆ y) 6 = (Phi θ x ⋆ Phi θ y) 6 := by
    simp only [Phi_coord_6, wit8Mul_coord_6, Phi_coord_0, Phi_coord_1,
      Phi_coord_2, Phi_coord_3, Phi_coord_4, Phi_coord_5, Phi_coord_7]
    linear_combination (-(x 2 * y 3) + x 3 * y 2 + x 4 * y 5 - x 5 * y 4) * hpy
  have h7 : Phi θ (x ⋆ y) 7 = (Phi θ x ⋆ Phi θ y) 7 := by
    simp only [Phi_coord_7, wit8Mul_coord_7, Phi_coord_0, Phi_coord_1,
      Phi_coord_2, Phi_coord_3, Phi_coord_4, Phi_coord_5, Phi_coord_6]
    linear_combination (x 2 * y 5 - x 3 * y 4 - x 4 * y 3 + x 5 * y 2) * hpy
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-! ### The candidate on the derived basis -/

@[simp] theorem Phi_w1 (θ : ℝ) : Phi θ w1 = w1 := by
  funext i; fin_cases i <;> simp [w1]

@[simp] theorem Phi_wA (θ : ℝ) : Phi θ wA = wA := by
  funext i; fin_cases i <;> simp [wA]

@[simp] theorem Phi_wB (θ : ℝ) : Phi θ wB = Real.cos θ • wB + Real.sin θ • wC := by
  funext i; fin_cases i <;> simp [wB, wC]

@[simp] theorem Phi_wC (θ : ℝ) :
    Phi θ wC = (- Real.sin θ) • wB + Real.cos θ • wC := by
  funext i; fin_cases i <;> simp [wB, wC]

@[simp] theorem Phi_wP (θ : ℝ) : Phi θ wP = Real.cos θ • wP + Real.sin θ • wQ := by
  funext i; fin_cases i <;> simp [wP, wQ]

@[simp] theorem Phi_wQ (θ : ℝ) :
    Phi θ wQ = (- Real.sin θ) • wP + Real.cos θ • wQ := by
  funext i; fin_cases i <;> simp [wP, wQ]

@[simp] theorem Phi_wR (θ : ℝ) : Phi θ wR = wR := by
  funext i; fin_cases i <;> simp [wR]

@[simp] theorem Phi_wS (θ : ℝ) : Phi θ wS = wS := by
  funext i; fin_cases i <;> simp [wS]

/-! ### Compatibility with the old carrier -/

theorem Phi_iota3 (θ : ℝ) (X : Vec4) : Phi θ (iota3 X) = iota3 (rot θ X) := by
  funext i
  fin_cases i <;> simp

/-- **EXISTENCE.**  The old axial rotation extends to a unital multiplicative
real-linear map of the whole carrier. -/
theorem Phi_isAxialExtension (θ : ℝ) : IsAxialExtension θ (Phi θ) where
  unital := Phi_w1 θ
  mul := Phi_mul θ
  old := Phi_iota3 θ

/-- **EXISTENCE AND UNIQUENESS TOGETHER.** -/
theorem axialExtension_existsUnique (θ : ℝ) :
    ∃! Φ : W →ₗ[ℝ] W, IsAxialExtension θ Φ :=
  ⟨Phi θ, Phi_isAxialExtension θ, fun _ hΨ => axialExtension_unique hΨ (Phi_isAxialExtension θ)⟩

/-- Any extension **is** the explicit one; the forced basis values of Step 1 are
therefore attained. -/
theorem eq_Phi_of_isAxialExtension {θ : ℝ} {Φ : W →ₗ[ℝ] W}
    (h : IsAxialExtension θ Φ) : Φ = Phi θ :=
  axialExtension_unique h (Phi_isAxialExtension θ)

/-! ## Step 4 — the one-parameter group law on the algebra -/

/-- **IDENTITY AT ZERO.** -/
theorem Phi_zero : Phi 0 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext i
  fin_cases i <;> simp

/-- **ADDITIVITY OF THE ANGLE ON THE WHOLE ALGEBRA.** -/
theorem Phi_add (θ φ : ℝ) : Phi (θ + φ) = (Phi θ).comp (Phi φ) := by
  refine LinearMap.ext fun x => ?_
  funext i
  fin_cases i <;>
    simp [Phi, PhiFun, Real.cos_add, Real.sin_add] <;> ring

theorem Phi_add_apply (θ φ : ℝ) (x : W) : Phi (θ + φ) x = Phi θ (Phi φ x) := by
  rw [Phi_add]; rfl

/-- **THE ALGEBRA AUTOMORPHISM RETURNS EXACTLY AFTER `2π`.** -/
theorem Phi_two_pi : Phi (2 * Real.pi) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext i
  fin_cases i <;> simp [Real.cos_two_pi, Real.sin_two_pi]

theorem Phi_four_pi : Phi (4 * Real.pi) = LinearMap.id := by
  have h : (4 : ℝ) * Real.pi = 2 * Real.pi + 2 * Real.pi := by ring
  rw [h, Phi_add, Phi_two_pi]
  rfl

/-- Each `Φθ` is bijective, with inverse `Φ(-θ)`. -/
theorem Phi_neg_comp (θ : ℝ) : (Phi (-θ)).comp (Phi θ) = LinearMap.id := by
  rw [← Phi_add]
  simp [Phi_zero]

theorem Phi_bijective (θ : ℝ) : Function.Bijective (Phi θ) := by
  constructor
  · intro x y hxy
    have h1 : Phi (-θ) (Phi θ x) = Phi (-θ) (Phi θ y) := by rw [hxy]
    have hx : Phi (-θ + θ) x = x := by rw [neg_add_cancel, Phi_zero]; rfl
    have hy : Phi (-θ + θ) y = y := by rw [neg_add_cancel, Phi_zero]; rfl
    rw [Phi_add_apply] at hx hy
    rw [← hx, ← hy, h1]
  · intro y
    refine ⟨Phi (-θ) y, ?_⟩
    have : Phi (θ + -θ) y = y := by rw [add_neg_cancel, Phi_zero]; rfl
    rwa [Phi_add_apply] at this

end NullSectorTask10
