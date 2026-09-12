import RequestProject.Experiment2.NullSectorTask01.Basic

/-!
# Task 04, Layer 1: the ambient 3+1 bilinear form obtained by polarization

Input data (and nothing else):

* the real carrier `Vec4 = ℝ × ℝ × ℝ × ℝ` (from `RequestProject.Experiment2.NullSectorTask01.Basic`);
* the quadratic form `Q4 (t,x,y,z) = t^2 - x^2 - y^2 - z^2` (same file);
* the ordinary real vector-space structure of `Vec4`.

`L4` is **defined** by polarization of `Q4`; its coordinate expression, its
bilinearity, its symmetry, the identity `L4 X X = Q4 X` and the uniqueness of a
symmetric bilinear form with the prescribed diagonal are all **derived**.

No product, no algebra, and no additional geometric datum occurs in this file.
-/

namespace NullSectorTask04

open NullSectorTask01

/-- Componentwise extensionality for the ambient carrier. -/
theorem vec4_ext {X Y : Vec4} (h1 : X.1 = Y.1) (h2 : X.2.1 = Y.2.1)
    (h3 : X.2.2.1 = Y.2.2.1) (h4 : X.2.2.2 = Y.2.2.2) : X = Y := by
  obtain ⟨a, b, c, d⟩ := X; obtain ⟨a', b', c', d'⟩ := Y
  simp_all

/-! ## Polarization -/

/-- Polarization of `Q4`.  Not an independent primitive. -/
noncomputable def L4 (X Y : Vec4) : ℝ := (Q4 (X + Y) - Q4 X - Q4 Y) / 2

/-- **Derived** coordinate expression of the polarization. -/
theorem L4_apply (t x y z t' x' y' z' : ℝ) :
    L4 (t, x, y, z) (t', x', y', z') = t * t' - x * x' - y * y' - z * z' := by
  simp [L4, Q4]; ring

@[simp] theorem L4_coord (X Y : Vec4) :
    L4 X Y = X.1 * Y.1 - X.2.1 * Y.2.1 - X.2.2.1 * Y.2.2.1 - X.2.2.2 * Y.2.2.2 := by
  obtain ⟨t, x, y, z⟩ := X; obtain ⟨t', x', y', z'⟩ := Y; exact L4_apply t x y z t' x' y' z'

theorem L4_symm (X Y : Vec4) : L4 X Y = L4 Y X := by simp; ring

theorem L4_add_left (X Y Z : Vec4) : L4 (X + Y) Z = L4 X Z + L4 Y Z := by simp; ring

theorem L4_add_right (X Y Z : Vec4) : L4 X (Y + Z) = L4 X Y + L4 X Z := by simp; ring

theorem L4_smul_left (c : ℝ) (X Y : Vec4) : L4 (c • X) Y = c * L4 X Y := by simp; ring

theorem L4_smul_right (c : ℝ) (X Y : Vec4) : L4 X (c • Y) = c * L4 X Y := by simp; ring

theorem L4_sub_left (X Y Z : Vec4) : L4 (X - Y) Z = L4 X Z - L4 Y Z := by simp; ring

theorem L4_sub_right (X Y Z : Vec4) : L4 X (Y - Z) = L4 X Y - L4 X Z := by simp; ring

theorem L4_neg_left (X Y : Vec4) : L4 (-X) Y = - L4 X Y := by simp; ring

theorem L4_neg_right (X Y : Vec4) : L4 X (-Y) = - L4 X Y := by simp; ring

@[simp] theorem L4_zero_left (Y : Vec4) : L4 0 Y = 0 := by simp

@[simp] theorem L4_zero_right (X : Vec4) : L4 X 0 = 0 := by simp

/-- The diagonal of the polarization recovers the quadratic form. -/
theorem L4_self (X : Vec4) : L4 X X = Q4 X := by
  obtain ⟨t, x, y, z⟩ := X; simp [Q4]; ring

/-- **Negative control (row 1).**  `Q4` determines its polarization: a symmetric
bilinear form whose diagonal is `Q4` is necessarily `L4`. -/
theorem L4_unique_of_diagonal (B : Vec4 → Vec4 → ℝ)
    (hsymm : ∀ X Y, B X Y = B Y X)
    (hadd : ∀ X Y Z, B (X + Y) Z = B X Z + B Y Z)
    (hdiag : ∀ X, B X X = Q4 X) : ∀ X Y, B X Y = L4 X Y := by
  intro X Y
  have h1 : B (X + Y) (X + Y) = Q4 (X + Y) := hdiag _
  have h2 : B (X + Y) (X + Y) = B X X + B Y X + (B X Y + B Y Y) := by
    rw [hadd X Y (X + Y)]
    have hx : B X (X + Y) = B X X + B Y X := by
      rw [hsymm X (X + Y), hadd X Y X, hsymm X X, hsymm Y X]
    have hy : B Y (X + Y) = B X Y + B Y Y := by
      rw [hsymm Y (X + Y), hadd X Y Y, hsymm X Y, hsymm Y Y]
    rw [hx, hy]
  rw [hdiag X, hdiag Y, hsymm Y X] at h2
  have h3 := h1.symm.trans h2
  simp only [L4]
  linarith

/-- Nondegeneracy of `L4` on the concrete carrier. -/
theorem L4_nondegenerate {X : Vec4} (h : ∀ Y, L4 X Y = 0) : X = 0 := by
  obtain ⟨t, x, y, z⟩ := X
  have h0 := h (1, 0, 0, 0)
  have h1 := h (0, 1, 0, 0)
  have h2 := h (0, 0, 1, 0)
  have h3 := h (0, 0, 0, 1)
  simp at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

/-! ## The chosen reference future unit -/

/-- The reference future unit fixed once and for all in Task 04. -/
def e₀ : Vec4 := (1, 0, 0, 0)

@[simp] theorem e₀_fst : e₀.1 = 1 := rfl
@[simp] theorem e₀_snd : e₀.2 = 0 := rfl

theorem smul_e₀ (a : ℝ) : a • e₀ = (a, 0, 0, 0) := by
  apply vec4_ext <;> simp [e₀]

@[simp] theorem Q4_e₀ : Q4 e₀ = 1 := by simp [Q4, e₀]

@[simp] theorem L4_e₀_left (X : Vec4) : L4 e₀ X = X.1 := by simp [e₀]

@[simp] theorem L4_e₀_right (X : Vec4) : L4 X e₀ = X.1 := by simp [e₀]

end NullSectorTask04
