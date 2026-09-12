import RequestProject.Experiment2.NullSectorTask10.AxisDecomposition

/-!
# Task 10, Layer 2: the old spatial rotation about the distinguished axis

The one-parameter family studied in Task 10 is the ordinary already-established
three-dimensional spatial rotation of the *old* carrier about the selected axis:
the time coordinate and the distinguished axis are fixed and the two remaining
old spatial directions rotate into each other.

Only elementary Mathlib trigonometric identities (`Real.cos_add`,
`Real.sin_add`, `Real.sin_sq_add_cos_sq`) are used.  No lift, no element of the
Task-08 algebra and no representation is introduced in this module.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## Definition -/

/-- **THE OLD AXIAL ROTATION.**  `rot θ` fixes the time coordinate and the
distinguished axis and rotates the transverse old plane by the angle `θ`. -/
noncomputable def rot (θ : ℝ) : Vec4 →ₗ[ℝ] Vec4 where
  toFun X := (X.1, X.2.1,
    Real.cos θ * X.2.2.1 - Real.sin θ * X.2.2.2,
    Real.sin θ * X.2.2.1 + Real.cos θ * X.2.2.2)
  map_add' := by intro X Y; simp [Prod.ext_iff]; constructor <;> ring
  map_smul' := by intro c X; simp [Prod.ext_iff]; constructor <;> ring

@[simp] theorem rot_apply (θ : ℝ) (X : Vec4) :
    rot θ X = (X.1, X.2.1,
      Real.cos θ * X.2.2.1 - Real.sin θ * X.2.2.2,
      Real.sin θ * X.2.2.1 + Real.cos θ * X.2.2.2) := rfl

/-! ## The required defining values -/

@[simp] theorem rot_e₀ (θ : ℝ) : rot θ e₀ = e₀ := by
  simp [e₀]

/-- **THE DISTINGUISHED AXIS IS FIXED.** -/
@[simp] theorem rot_axis (θ : ℝ) : rot θ axis = axis := by
  simp [axis, dirA, sp, s₁]

@[simp] theorem rot_dirA (θ : ℝ) : rot θ dirA = dirA := rot_axis θ

/-- **THE TRANSVERSE ACTION**, exactly as prescribed. -/
@[simp] theorem rot_dirB (θ : ℝ) :
    rot θ dirB = Real.cos θ • dirB + Real.sin θ • dirC := by
  simp [dirB, dirC, sp, s₂, s₃]

@[simp] theorem rot_dirC (θ : ℝ) :
    rot θ dirC = (- Real.sin θ) • dirB + Real.cos θ • dirC := by
  simp [dirB, dirC, sp, s₂, s₃]

/-! ## The one-parameter group law -/

/-- **IDENTITY AT ZERO.** -/
theorem rot_zero : rot 0 = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp

/-- **ADDITIVITY OF THE ANGLE.** -/
theorem rot_add (θ φ : ℝ) : rot (θ + φ) = (rot θ).comp (rot φ) := by
  refine LinearMap.ext fun X => ?_
  simp only [rot_apply, LinearMap.comp_apply, Real.cos_add, Real.sin_add,
    Prod.mk.injEq]
  exact ⟨trivial, trivial, by ring, by ring⟩

theorem rot_add_apply (θ φ : ℝ) (X : Vec4) : rot (θ + φ) X = rot θ (rot φ X) := by
  rw [rot_add]; rfl

/-- Rotation by a full turn is the identity of the old carrier. -/
theorem rot_two_pi : rot (2 * Real.pi) = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp [Real.cos_two_pi, Real.sin_two_pi]

/-! ## Invariance of the inherited Lorentz form -/

/-- **THE INHERITED 3+1 FORM IS PRESERVED.** -/
theorem Q4_rot (θ : ℝ) (X : Vec4) : Q4 (rot θ X) = Q4 X := by
  simp only [Q4, rot_apply]
  linear_combination (- X.2.2.1 ^ 2 - X.2.2.2 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- The inherited Euclidean rest form is preserved as well. -/
theorem dot3_rot (θ : ℝ) (X Y : Vec4) :
    dot3 (rot θ X).2 (rot θ Y).2 = dot3 X.2 Y.2 := by
  simp only [rot_apply, dot3_apply]
  linear_combination (X.2.2.1 * Y.2.2.1 + X.2.2.2 * Y.2.2.2) * Real.sin_sq_add_cos_sq θ

/-! ## Sector preservation at the old-carrier level -/

theorem rot_mem_Long {X : Vec4} (θ : ℝ) (hX : X ∈ Long) : rot θ X ∈ Long := by
  rw [Long_coords] at hX ⊢
  have h2 : X.2.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.1) hX; simpa using this
  have h3 : X.2.2.2 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.2) hX; simpa using this
  have h0 : X.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.1) hX; simpa using this
  simp [h0, h2, h3]

theorem rot_mem_Trans {X : Vec4} (θ : ℝ) (hX : X ∈ Trans) : rot θ X ∈ Trans := by
  rw [Trans_coords] at hX ⊢
  have h0 : X.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.1) hX; simpa using this
  have h1 : X.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.1) hX; simpa using this
  simp [h0, h1]

end NullSectorTask10
