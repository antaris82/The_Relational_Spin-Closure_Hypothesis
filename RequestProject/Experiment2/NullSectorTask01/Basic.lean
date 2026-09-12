import Mathlib

/-!
# Task 01, Layer 1: the ambient 3+1 carrier and the longitudinal 1+1 subspace

Purely algebraic/kinematic set-up.  No dynamical or physical structure is attached
to any of the objects defined here; they are real vector spaces equipped with
quadratic forms.
-/

namespace NullSectorTask01

/-- Ambient real 3+1 carrier, coordinates written `(t, x, y, z)`. -/
abbrev Vec4 : Type := ℝ × ℝ × ℝ × ℝ

/-- Longitudinal 1+1 carrier, coordinates written `(t, x)`. -/
abbrev Long : Type := ℝ × ℝ

/-- The Lorentz quadratic form of signature `(+,-,-,-)` on `Vec4`. -/
def Q4 (X : Vec4) : ℝ := X.1 ^ 2 - X.2.1 ^ 2 - X.2.2.1 ^ 2 - X.2.2.2 ^ 2

/-- The Lorentz quadratic form of signature `(+,-)` on `Long`. -/
def Q2 (X : Long) : ℝ := X.1 ^ 2 - X.2 ^ 2

/-- The canonical embedding of the longitudinal plane `y = z = 0` into `Vec4`. -/
def iota (X : Long) : Vec4 := (X.1, X.2, 0, 0)

@[simp] theorem Q4_apply (t x y z : ℝ) : Q4 (t, x, y, z) = t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := rfl

@[simp] theorem Q2_apply (t x : ℝ) : Q2 (t, x) = t ^ 2 - x ^ 2 := rfl

@[simp] theorem iota_apply (t x : ℝ) : iota (t, x) = (t, x, 0, 0) := rfl

/-- `iota` is an injective linear map (stated concretely). -/
theorem iota_injective : Function.Injective iota := by
  rintro ⟨t, x⟩ ⟨s, y⟩ h
  simp only [iota, Prod.mk.injEq] at h
  simp [h.1, h.2.1]

/-- **Acceptance criterion 1.**  The longitudinal quadratic form is exactly the
restriction of the ambient 3+1 Lorentz form along the canonical embedding. -/
theorem Q4_iota (X : Long) : Q4 (iota X) = Q2 X := by
  obtain ⟨t, x⟩ := X
  simp [Q4, Q2, iota]

end NullSectorTask01
