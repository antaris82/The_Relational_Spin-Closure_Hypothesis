import RequestProject.Experiment2.NullSectorTask04.Lorentz4

/-!
# Task 04, Layer 2: the rest space of the chosen unit and its positive form

Everything here is derived from `Q4`, its polarization `L4`, and the single
chosen vector `e₀`.  No second metric is inserted: the Euclidean form `h` is
*defined* as `-L4` and its coordinate description as the ordinary
three-dimensional dot product is *proved*.
-/

namespace NullSectorTask04

open NullSectorTask01

/-! ## The rest space -/

/-- The rest subspace attached to `e₀`, defined by `L4`-orthogonality. -/
def IsRest (X : Vec4) : Prop := L4 e₀ X = 0

/-- **Coordinate characterisation** of the rest space. -/
theorem isRest_iff (X : Vec4) : IsRest X ↔ X.1 = 0 := by
  simp [IsRest]

/-- The rest space as a submodule, defined by the `L4`-orthogonality condition. -/
noncomputable def Rest : Submodule ℝ Vec4 where
  carrier := {X | IsRest X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, isRest_iff] at *
    simp [ha, hb]
  zero_mem' := by simp [Set.mem_setOf_eq, isRest_iff]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, isRest_iff] at *
    simp [ha]

@[simp] theorem mem_Rest (X : Vec4) : X ∈ Rest ↔ X.1 = 0 := isRest_iff X

/-! ## Spatial coordinates -/

/-- Coordinate carrier of the rest space. -/
abbrev Vec3 : Type := ℝ × ℝ × ℝ

/-- The embedding of spatial coordinates into `Vec4`. -/
def sp (v : Vec3) : Vec4 := (0, v)

@[simp] theorem sp_apply (v : Vec3) : sp v = (0, v) := rfl
@[simp] theorem sp_fst (v : Vec3) : (sp v).1 = 0 := rfl
@[simp] theorem sp_snd (v : Vec3) : (sp v).2 = v := rfl

theorem sp_mem_Rest (v : Vec3) : sp v ∈ Rest := by simp

/-- Every rest vector is `sp` of its spatial part; `sp` is a bijection onto `Rest`. -/
theorem rest_eq_sp {X : Vec4} (hX : X ∈ Rest) : X = sp X.2 := by
  obtain ⟨t, v⟩ := X
  simp only [mem_Rest] at hX
  simp [sp, hX]

theorem sp_injective : Function.Injective sp := by
  intro v w h
  simpa [sp, Prod.ext_iff] using h

theorem range_sp : Set.range sp = (Rest : Set Vec4) := by
  ext X
  constructor
  · rintro ⟨v, rfl⟩; exact sp_mem_Rest v
  · intro hX; exact ⟨X.2, (rest_eq_sp hX).symm⟩

theorem sp_add (v w : Vec3) : sp (v + w) = sp v + sp w := by
  simp [sp]

theorem sp_smul (c : ℝ) (v : Vec3) : sp (c • v) = c • sp v := by
  simp [sp]

/-- `sp` packaged as a linear map. -/
def spL : Vec3 →ₗ[ℝ] Vec4 where
  toFun := sp
  map_add' := sp_add
  map_smul' := sp_smul

@[simp] theorem spL_apply (v : Vec3) : spL v = sp v := rfl

/-- Decomposition of an arbitrary ambient vector into its `e₀`-component and its
rest component. -/
theorem vec4_decomp (X : Vec4) : X = X.1 • e₀ + sp X.2 := by
  obtain ⟨t, v⟩ := X
  simp [e₀, sp, Prod.ext_iff]

/-! ## The induced positive form -/

/-- The ordinary three-dimensional dot product of spatial coordinates. -/
def dot3 (v w : Vec3) : ℝ := v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2

@[simp] theorem dot3_apply (v w : Vec3) :
    dot3 v w = v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2 := rfl

theorem dot3_symm (v w : Vec3) : dot3 v w = dot3 w v := by simp; ring

theorem dot3_add_left (u v w : Vec3) : dot3 (u + v) w = dot3 u w + dot3 v w := by simp; ring

theorem dot3_add_right (u v w : Vec3) : dot3 u (v + w) = dot3 u v + dot3 u w := by simp; ring

theorem dot3_sub_left (u v w : Vec3) : dot3 (u - v) w = dot3 u w - dot3 v w := by simp; ring

theorem dot3_smul_left (c : ℝ) (v w : Vec3) : dot3 (c • v) w = c * dot3 v w := by simp; ring

theorem dot3_smul_right (c : ℝ) (v w : Vec3) : dot3 v (c • w) = c * dot3 v w := by simp; ring

/-- The induced form on the rest space, defined from `L4` alone. -/
noncomputable def h (X Y : Vec4) : ℝ := - L4 X Y

/-- **Derived.**  On the rest space `h` is the ordinary three-dimensional dot
product of the spatial coordinates. -/
theorem h_sp (v w : Vec3) : h (sp v) (sp w) = dot3 v w := by
  simp [h, sp]; ring

/-- The diagonal of `h` is minus `Q4`. -/
theorem h_self (X : Vec4) : h X X = - Q4 X := by rw [h, L4_self]

/-- **Positivity** of the induced form on the rest space. -/
theorem h_nonneg {X : Vec4} (hX : X ∈ Rest) : 0 ≤ h X X := by
  rw [rest_eq_sp hX, h_sp]
  have := sq_nonneg X.2.1
  have := sq_nonneg X.2.2.1
  have := sq_nonneg X.2.2.2
  simp only [dot3_apply]
  nlinarith

/-- **Characterisation of equality** in the positivity statement. -/
theorem h_eq_zero_iff {X : Vec4} (hX : X ∈ Rest) : h X X = 0 ↔ X = 0 := by
  obtain ⟨t, a, b, c⟩ := X
  simp only [mem_Rest] at hX
  subst hX
  constructor
  · intro hz
    simp [h] at hz
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    simp [ha, hb, hc, Prod.ext_iff]
  · intro hz
    simp [Prod.ext_iff] at hz
    simp [h, hz.1, hz.2.1, hz.2.2]

theorem dot3_self_nonneg (v : Vec3) : 0 ≤ dot3 v v := by
  simp only [dot3_apply]; nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]

theorem dot3_self_eq_zero_iff (v : Vec3) : dot3 v v = 0 ↔ v = 0 := by
  obtain ⟨a, b, c⟩ := v
  constructor
  · intro hz
    simp only [dot3_apply] at hz
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    simp [ha, hb, hc, Prod.ext_iff]
  · intro hz
    simp [Prod.ext_iff] at hz
    simp [hz.1, hz.2.1, hz.2.2]

/-- `Q4` of a rest vector is minus its Euclidean square. -/
theorem Q4_sp (v : Vec3) : Q4 (sp v) = - dot3 v v := by
  simp [Q4, sp]; ring

/-- The spatial coordinate basis. -/
def s₁ : Vec3 := (1, 0, 0)
def s₂ : Vec3 := (0, 1, 0)
def s₃ : Vec3 := (0, 0, 1)

@[simp] theorem dot3_s₁_s₁ : dot3 s₁ s₁ = 1 := by norm_num [s₁]
@[simp] theorem dot3_s₂_s₂ : dot3 s₂ s₂ = 1 := by norm_num [s₂]
@[simp] theorem dot3_s₃_s₃ : dot3 s₃ s₃ = 1 := by norm_num [s₃]

/-- Coordinate decomposition of a spatial vector. -/
theorem vec3_decomp (v : Vec3) : v = v.1 • s₁ + v.2.1 • s₂ + v.2.2 • s₃ := by
  obtain ⟨a, b, c⟩ := v
  simp [s₁, s₂, s₃]

end NullSectorTask04
