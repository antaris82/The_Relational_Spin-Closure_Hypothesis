import RequestProject.Experiment2.NullSectorTask09.CentralPlane

/-!
# Task 09, Layer 3: Phase B — the unknown central-valued quadratic map

An **entirely unknown** map is introduced.  No candidate, no coordinate
polynomial, no formula of any kind appears in this module or in the rigidity
module that follows it; the first explicit map is constructed only in
`Existence.lean`, after the rigidity theorem.

Two equivalent formulations are given:

* the working one, `CentralQuadraticExtension N` for `N : W → W` together with
  the requirement that every value lies in the central plane `Z`;
* the literal one, `CentralQuadraticExtensionZ N` for `N : W → Z` with the
  induced multiplication of `Z`.

`cqeZ_iff` proves that the two are the same condition, so nothing is lost by
working with the first.
-/

namespace NullSectorTask09

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08

/-- **PHASE B hypothesis set (working form).**  An unknown map of the carrier
into itself which is real-quadratic, takes all its values in the internally
derived central plane, is multiplicative for the inherited product, and
restricts to the inherited Lorentz form on the embedded old carrier. -/
structure CentralQuadraticExtension (N : W → W) : Prop where
  /-- QUADRATIC. -/
  quad : IsRealQuadratic N
  /-- CENTRAL CODOMAIN. -/
  mem : ∀ x : W, N x ∈ Z
  /-- MULTIPLICATIVE. -/
  mul : ∀ x y : W, N (x ⋆ y) = N x ⋆ N y
  /-- OLD-`Q4` RESTRICTION. -/
  ext : ∀ X : Vec4, N (iota3 X) = Q4 X • w1

namespace CentralQuadraticExtension

variable {N : W → W} (h : CentralQuadraticExtension N)
include h

theorem map_zero : N 0 = 0 := h.quad.map_zero

/-- **FORCED.**  The value on the unit. -/
theorem val_w1 : N w1 = w1 := by
  have hx := h.ext e₀
  rw [iota3_e₀, Q4_e₀] at hx
  simpa using hx

/-- The polarization takes its values in the central plane as well. -/
theorem polar_mem (x y : W) : polar N x y ∈ Z := by
  have : polar N x y = N (x + y) - N x - N y := rfl
  rw [this]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ (h.mem _) (h.mem _)) (h.mem _)

/-- **COVARIANCE OF THE POLARIZATION.**  Multiplying both arguments by a fixed
element multiplies the polarization by the value of the map at that element. -/
theorem polar_covariant (g x y : W) :
    polar N (g ⋆ x) (g ⋆ y) = N g ⋆ polar N x y := by
  have hadd : g ⋆ x + g ⋆ y = g ⋆ (x + y) := (mul_add_W g x y).symm
  simp only [polar, hadd, h.mul]
  rw [map_sub, map_sub]

/-- The form of covariance actually used: `polar N u (u ⋆ w)` is reduced to a
polarization against the unit. -/
theorem polar_pair (u w : W) : polar N u (u ⋆ w) = N u ⋆ polar N w1 w := by
  have := h.polar_covariant u w1 w
  rwa [mul_one_W] at this

/-- The map is determined by its polarization. -/
theorem eq_half_polar (x : W) : N x = ((2 : ℝ)⁻¹) • polar N x x :=
  h.quad.eq_half_polar x

end CentralQuadraticExtension

/-! ## The literal `W → Z` formulation -/

/-- The multiplication induced on the central plane by the inherited product. -/
def Zmul (u v : (Z : Submodule ℝ W)) : (Z : Submodule ℝ W) :=
  ⟨(u : W) ⋆ (v : W), Z_mul_mem u.2 v.2⟩

@[simp] theorem Zmul_coe (u v : (Z : Submodule ℝ W)) :
    ((Zmul u v : (Z : Submodule ℝ W)) : W) = (u : W) ⋆ (v : W) := rfl

/-- The unit of the central plane. -/
def Zone : (Z : Submodule ℝ W) := ⟨w1, w1_mem_Z⟩

@[simp] theorem Zone_coe : ((Zone : (Z : Submodule ℝ W)) : W) = w1 := rfl

/-- **PHASE B hypothesis set (literal form).**  An unknown map `N : W → Z`. -/
structure CentralQuadraticExtensionZ (N : W → (Z : Submodule ℝ W)) : Prop where
  /-- QUADRATIC. -/
  quad : IsRealQuadratic N
  /-- MULTIPLICATIVE for the induced multiplication of `Z`. -/
  mul : ∀ x y : W, N (x ⋆ y) = Zmul (N x) (N y)
  /-- OLD-`Q4` RESTRICTION. -/
  ext : ∀ X : Vec4, N (iota3 X) = Q4 X • Zone

theorem polar_coe (N : W → (Z : Submodule ℝ W)) (x y : W) :
    polar (fun x => ((N x : W))) x y = ((polar N x y : (Z : Submodule ℝ W)) : W) := by
  simp [polar]

/-- **THE TWO FORMULATIONS AGREE.** -/
theorem cqeZ_iff (N : W → (Z : Submodule ℝ W)) :
    CentralQuadraticExtensionZ N ↔
      CentralQuadraticExtension (fun x => ((N x : W))) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, fun x => (N x).2, ?_, ?_⟩
    · intro r x
      rw [h.quad.homog r x]; rfl
    · intro x y z
      rw [polar_coe, polar_coe, polar_coe, h.quad.polar_add_left]; rfl
    · intro r x y
      rw [polar_coe, polar_coe, h.quad.polar_smul_left]; rfl
    · intro x y
      rw [h.mul x y]; rfl
    · intro X
      rw [h.ext X]; rfl
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro r x
      apply Subtype.ext
      have := h.quad.homog r x
      simpa using this
    · intro x y z
      apply Subtype.ext
      have := h.quad.polar_add_left x y z
      rw [polar_coe, polar_coe, polar_coe] at this
      simpa using this
    · intro r x y
      apply Subtype.ext
      have := h.quad.polar_smul_left r x y
      rw [polar_coe, polar_coe] at this
      simpa using this
    · intro x y
      apply Subtype.ext
      simpa using h.mul x y
    · intro X
      apply Subtype.ext
      simpa using h.ext X

end NullSectorTask09
