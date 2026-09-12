import RequestProject.Experiment2.NullSectorTask01.Basic

/-!
# Task 02, Layer 1: the Lorentz bilinear form obtained by polarization

Input data (and nothing else):

* the real carrier `Long = ℝ × ℝ` (from `RequestProject.Experiment2.NullSectorTask01.Basic`);
* the quadratic form `Q2 (t,x) = t^2 - x^2` (same file);
* the ordinary real vector-space structure of `Long`.

The bilinear form `L2` is *defined* by polarization of `Q2` and its coordinate
expression is *derived*.  No algebra multiplication occurs in this file.
-/

namespace NullSectorTask02

open NullSectorTask01

/-- Polarization of `Q2`. -/
noncomputable def L2 (X Y : Long) : ℝ := (Q2 (X + Y) - Q2 X - Q2 Y) / 2

/-- **Derived** coordinate expression of the polarization. -/
theorem L2_apply (t x s y : ℝ) : L2 (t, x) (s, y) = t * s - x * y := by
  simp [L2, Q2]
  ring

@[simp] theorem L2_coord (X Y : Long) : L2 X Y = X.1 * Y.1 - X.2 * Y.2 := by
  obtain ⟨t, x⟩ := X; obtain ⟨s, y⟩ := Y; exact L2_apply t x s y

theorem L2_symm (X Y : Long) : L2 X Y = L2 Y X := by simp; ring

theorem L2_add_left (X Y Z : Long) : L2 (X + Y) Z = L2 X Z + L2 Y Z := by
  simp; ring

theorem L2_add_right (X Y Z : Long) : L2 X (Y + Z) = L2 X Y + L2 X Z := by
  simp; ring

theorem L2_smul_left (c : ℝ) (X Y : Long) : L2 (c • X) Y = c * L2 X Y := by
  simp; ring

theorem L2_smul_right (c : ℝ) (X Y : Long) : L2 X (c • Y) = c * L2 X Y := by
  simp; ring

theorem L2_neg_left (X Y : Long) : L2 (-X) Y = -L2 X Y := by simp; ring

theorem L2_sub_left (X Y Z : Long) : L2 (X - Y) Z = L2 X Z - L2 Y Z := by
  simp; ring

theorem L2_sub_right (X Y Z : Long) : L2 X (Y - Z) = L2 X Y - L2 X Z := by
  simp; ring

@[simp] theorem L2_zero_left (Y : Long) : L2 0 Y = 0 := by simp

@[simp] theorem L2_zero_right (X : Long) : L2 X 0 = 0 := by simp

/-- `L2` restricted to the diagonal recovers `Q2`. -/
theorem L2_self (X : Long) : L2 X X = Q2 X := by
  obtain ⟨t, x⟩ := X; simp [Q2]; ring

/-- Nondegeneracy of `L2` on the concrete carrier. -/
theorem L2_nondegenerate {X : Long} (h : ∀ Y, L2 X Y = 0) : X = 0 := by
  obtain ⟨t, x⟩ := X
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  simp at h1 h2
  simp [h1, h2]

/-- The chosen reference vector of the coordinate carrier (an *additional datum*,
not something singled out by `Q2`). -/
def u₀ : Long := (1, 0)

/-- The second coordinate vector. -/
def s₀ : Long := (0, 1)

@[simp] theorem u₀_fst : u₀.1 = 1 := rfl
@[simp] theorem u₀_snd : u₀.2 = 0 := rfl
@[simp] theorem s₀_fst : s₀.1 = 0 := rfl
@[simp] theorem s₀_snd : s₀.2 = 1 := rfl

@[simp] theorem Q2_u₀ : Q2 u₀ = 1 := by simp [Q2, u₀]
@[simp] theorem Q2_s₀ : Q2 s₀ = -1 := by simp [Q2, s₀]
@[simp] theorem L2_u₀_s₀ : L2 u₀ s₀ = 0 := by simp [u₀, s₀]

/-- Coordinate decomposition along the chosen coordinate vectors. -/
theorem coord_decomp (X : Long) : X = X.1 • u₀ + X.2 • s₀ := by
  obtain ⟨t, x⟩ := X
  apply Prod.ext <;> simp [u₀, s₀]

end NullSectorTask02
