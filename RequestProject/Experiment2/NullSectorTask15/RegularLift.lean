import RequestProject.Experiment2.NullSectorTask15.SafeBase

/-!
# Task 15, Layer 1 (§III): regular one-axis lifts and their exact classification

For a fixed unit spatial axis `n` an **axis lift** is an arbitrary one-parameter family of
carrier elements implementing the inherited automorphism family `PhiGen n θ` by
conjugation, normalized at `θ = 0` and obeying the one-axis group law.  Nothing else is
assumed: no membership in any subspace, no exponential form, no continuity.

The results of this layer are

* **unique factorization** — every axis lift is uniquely `U θ = z θ ⋆ Un n θ` with `z`
  taking values in the exact centre and multiplicative (`axisLift_iff`,
  `axisLift_residual_unique`);
* **exact continuous classification** — a *continuous* axis lift is exactly
  `U θ = zexp α(n) β(n) θ ⋆ Un n θ` for a unique pair of real numbers
  (`continuousAxisLift_classification`, `continuousAxisLift_parameters_unique`);
* **the stronger differentiable layer adds nothing** — every continuous axis lift is
  automatically differentiable (`continuousAxisLift_differentiable`).

No exponential form is prescribed anywhere: the exponential–rotation shape is *derived*
from continuity through the inherited one-axis coefficient classification.
-/

namespace NullSectorTask15

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14

/-! ## §III — the neutral definition of a regular axis lift -/

/-- **NEUTRAL DEFINITION (§III).**  An internal implementation of the inherited
automorphism family of the axis `n`: a one-parameter family of carrier elements, normalized
at the identity, obeying the one-axis group law, and implementing `PhiGen n θ` by
conjugation.  No regularity and no shape assumption. -/
structure IsAxisLift (n : Vec3) (U : ℝ → W) : Prop where
  /-- Normalization at the identity parameter. -/
  unit : U 0 = w1
  /-- The already established one-axis group law. -/
  group : ∀ θ φ : ℝ, U (θ + φ) = U θ ⋆ U φ
  /-- The conjugation action is the inherited automorphism family. -/
  conj : ∀ (θ : ℝ) (x : W), (U θ ⋆ x) ⋆ U (-θ) = PhiGen n θ x

/-- **NEUTRAL DEFINITION (§III, first regularity layer).**  A continuous axis lift. -/
structure IsContinuousAxisLift (n : Vec3) (U : ℝ → W) : Prop extends IsAxisLift n U where
  /-- Continuity in the inherited finite-dimensional real topology of the carrier. -/
  cont : Continuous U

namespace IsAxisLift

variable {n : Vec3} {U : ℝ → W} (hU : IsAxisLift n U)
include hU

/-- **DERIVED.**  The two-sided inverse law follows from the group law. -/
theorem mul_neg (θ : ℝ) : U θ ⋆ U (-θ) = w1 := by
  have h := hU.group θ (-θ)
  rw [add_neg_cancel, hU.unit] at h
  exact h.symm

/-- **DERIVED.**  The other-sided inverse law. -/
theorem neg_mul (θ : ℝ) : U (-θ) ⋆ U θ = w1 := by
  have h := hU.group (-θ) θ
  rw [neg_add_cancel, hU.unit] at h
  exact h.symm

/-- **DERIVED.**  An axis lift implements the inherited automorphism in the sense of the
inherited `Implements` relation. -/
theorem implements (θ : ℝ) : Implements (U θ) (U (-θ)) (PhiGen n θ) where
  inv_right := hU.mul_neg θ
  inv_left := hU.neg_mul θ
  conj := hU.conj θ

end IsAxisLift

/-! ## The unique central residual -/

/-- **DERIVED.**  The candidate residual factor of an axis lift. -/
noncomputable def residual (n : Vec3) (U : ℝ → W) (θ : ℝ) : W := U θ ⋆ Un n (-θ)

/-- **PRINCIPAL THEOREM (§III), unique factorization.**  Every axis lift factors through
the inherited reference implementation with a multiplicative central residual, and
conversely every such factorization is an axis lift. -/
theorem axisLift_iff {n : Vec3} (hn : IsUnitAxis n) (U : ℝ → W) :
    IsAxisLift n U ↔ ∃ z : ℝ → W, IsCentralHom z ∧ ∀ θ, U θ = z θ ⋆ Un n θ := by
  constructor
  · intro hU
    have hmem : ∀ θ : ℝ, residual n U θ ∈ Z := fun θ =>
      implements_defect_mem_Z (hU.implements θ) (Un_implements hn θ)
    have hfac : ∀ θ : ℝ, U θ = residual n U θ ⋆ Un n θ := by
      intro θ
      rw [residual, mul_assoc_W, Un_neg_mul hn, mul_one_W]
    refine ⟨residual n U, ⟨fun θ => ?_, ?_, fun θ φ => ?_⟩, hfac⟩
    · rw [center_eq_Z]; exact hmem θ
    · rw [residual, hU.unit, neg_zero, Un_zero, one_mul_W]
    · have hUn : Un n (-(θ + φ)) = Un n (-φ) ⋆ Un n (-θ) := by
        rw [← Un_group hn]; ring_nf
      calc residual n U (θ + φ) = (U θ ⋆ U φ) ⋆ (Un n (-φ) ⋆ Un n (-θ)) := by
            rw [residual, hU.group, hUn]
        _ = U θ ⋆ (residual n U φ ⋆ Un n (-θ)) := by
            simp only [residual, mul_assoc_W]
        _ = U θ ⋆ (Un n (-θ) ⋆ residual n U φ) := by rw [Z_central (hmem φ)]
        _ = residual n U θ ⋆ residual n U φ := by simp only [residual, mul_assoc_W]
  · rintro ⟨z, hz, hU⟩
    have hzZ : ∀ θ : ℝ, z θ ∈ Z := fun θ => by
      have := hz.mem θ; rwa [center_eq_Z] at this
    have hinv : ∀ θ : ℝ, z θ ⋆ z (-θ) = w1 := by
      intro θ
      have := hz.mul θ (-θ)
      rw [add_neg_cancel, hz.unit] at this
      exact this.symm
    refine ⟨?_, fun θ φ => ?_, fun θ x => ?_⟩
    · rw [hU, hz.unit, Un_zero, one_mul_W]
    · rw [hU, hU, hU, hz.mul, Un_group hn]
      calc (z θ ⋆ z φ) ⋆ (Un n θ ⋆ Un n φ)
          = z θ ⋆ ((z φ ⋆ Un n θ) ⋆ Un n φ) := by simp only [mul_assoc_W]
        _ = z θ ⋆ ((Un n θ ⋆ z φ) ⋆ Un n φ) := by rw [Z_central (hzZ φ)]
        _ = (z θ ⋆ Un n θ) ⋆ (z φ ⋆ Un n φ) := by simp only [mul_assoc_W]
    · rw [hU, hU]
      calc ((z θ ⋆ Un n θ) ⋆ x) ⋆ (z (-θ) ⋆ Un n (-θ))
          = (z θ ⋆ z (-θ)) ⋆ (((Un n θ ⋆ x)) ⋆ Un n (-θ)) := by
            rw [show (z θ ⋆ Un n θ) ⋆ x = z θ ⋆ (Un n θ ⋆ x) from mul_assoc_W _ _ _]
            calc (z θ ⋆ (Un n θ ⋆ x)) ⋆ (z (-θ) ⋆ Un n (-θ))
                = z θ ⋆ (((Un n θ ⋆ x) ⋆ z (-θ)) ⋆ Un n (-θ)) := by simp only [mul_assoc_W]
              _ = z θ ⋆ ((z (-θ) ⋆ (Un n θ ⋆ x)) ⋆ Un n (-θ)) := by
                  rw [← Z_central (hzZ (-θ))]
              _ = (z θ ⋆ z (-θ)) ⋆ ((Un n θ ⋆ x) ⋆ Un n (-θ)) := by simp only [mul_assoc_W]
        _ = PhiGen n θ x := by rw [hinv, one_mul_W]; rfl

/-- **PRINCIPAL THEOREM (§III), uniqueness of the residual.**  The central residual of an
axis lift is unique: two factorizations through the reference implementation agree. -/
theorem axisLift_residual_unique {n : Vec3} (hn : IsUnitAxis n) {U : ℝ → W} {z z' : ℝ → W}
    (h : ∀ θ, U θ = z θ ⋆ Un n θ) (h' : ∀ θ, U θ = z' θ ⋆ Un n θ) : z = z' := by
  funext θ
  exact Un_right_cancel hn ((h θ).symm.trans (h' θ))

/-! ## Expansion of a central multiple of the reference implementation -/

/-- **DERIVED.**  The product of a central element with the reference implementation of an
arbitrary axis, expanded in four inherited directions. -/
theorem zc_mul_Un (n : Vec3) (a b θ : ℝ) :
    zc a b ⋆ Un n θ =
      (a * Real.cos (θ / 2)) • w1 + (b * Real.cos (θ / 2)) • wS
        + (-(a * Real.sin (θ / 2))) • Jmap n + (b * Real.sin (θ / 2)) • spat n := by
  funext i
  fin_cases i <;>
    simp [zc, Un, Jmap, spat, sp, w1, wS, wP, wQ, wR] <;> ring

@[simp] theorem zc_mul_Un_coord_0 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 0 = a * Real.cos (θ / 2) := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]

@[simp] theorem zc_mul_Un_coord_7 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 7 = b * Real.cos (θ / 2) := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]

theorem zc_mul_Un_coord_1 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 1 = b * Real.sin (θ / 2) * n.1 := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]; ring

theorem zc_mul_Un_coord_2 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 2 = b * Real.sin (θ / 2) * n.2.1 := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]; ring

theorem zc_mul_Un_coord_3 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 3 = b * Real.sin (θ / 2) * n.2.2 := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]; ring

theorem zc_mul_Un_coord_4 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 4 = -(a * Real.sin (θ / 2)) * n.2.2 := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]; ring

theorem zc_mul_Un_coord_5 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 5 = a * Real.sin (θ / 2) * n.2.1 := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]; ring

theorem zc_mul_Un_coord_6 (n : Vec3) (a b θ : ℝ) :
    (zc a b ⋆ Un n θ) 6 = -(a * Real.sin (θ / 2)) * n.1 := by
  simp [zc, Un, Jmap, w1, wS, wP, wQ, wR]; ring

/-- **DERIVED.**  Continuity of the reference implementation and of every central multiple
of it. -/
theorem continuous_zc_mul_Un (n : Vec3) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun θ => zc (f θ) (g θ) ⋆ Un n θ := by
  have he : (fun θ => zc (f θ) (g θ) ⋆ Un n θ) = fun θ =>
      (f θ * Real.cos (θ / 2)) • w1 + (g θ * Real.cos (θ / 2)) • wS
        + (-(f θ * Real.sin (θ / 2))) • Jmap n + (g θ * Real.sin (θ / 2)) • spat n := by
    funext θ; exact zc_mul_Un n (f θ) (g θ) θ
  rw [he]
  have h1 : Continuous fun θ : ℝ => f θ * Real.cos (θ / 2) := by fun_prop
  have h2 : Continuous fun θ : ℝ => g θ * Real.cos (θ / 2) := by fun_prop
  have h3 : Continuous fun θ : ℝ => -(f θ * Real.sin (θ / 2)) := by fun_prop
  have h4 : Continuous fun θ : ℝ => g θ * Real.sin (θ / 2) := by fun_prop
  exact (((h1.smul continuous_const).add (h2.smul continuous_const)).add
    (h3.smul continuous_const)).add (h4.smul continuous_const)

/-- **DERIVED.**  The two central coefficients are recovered from the coordinates of the
lift by an explicit continuous formula; the unit axis relation is what makes the recovery
exact. -/
theorem residual_coeffs_of_coords {n : Vec3} (hn : IsUnitAxis n) (a b θ : ℝ) :
    a = Real.cos (θ / 2) * (zc a b ⋆ Un n θ) 0
        - Real.sin (θ / 2) * (n.1 * (zc a b ⋆ Un n θ) 6 - n.2.1 * (zc a b ⋆ Un n θ) 5
            + n.2.2 * (zc a b ⋆ Un n θ) 4) ∧
      b = Real.cos (θ / 2) * (zc a b ⋆ Un n θ) 7
        + Real.sin (θ / 2) * (n.1 * (zc a b ⋆ Un n θ) 1 + n.2.1 * (zc a b ⋆ Un n θ) 2
            + n.2.2 * (zc a b ⋆ Un n θ) 3) := by
  have hnn : n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
    have := hn
    simp only [IsUnitAxis, h3, dot3_apply] at this
    nlinarith [this]
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  rw [zc_mul_Un_coord_0, zc_mul_Un_coord_1, zc_mul_Un_coord_2, zc_mul_Un_coord_3,
    zc_mul_Un_coord_4, zc_mul_Un_coord_5, zc_mul_Un_coord_6, zc_mul_Un_coord_7]
  constructor
  · linear_combination (-a) * hpy + (-(a * Real.sin (θ / 2) ^ 2)) * hnn
  · linear_combination (-b) * hpy + (-(b * Real.sin (θ / 2) ^ 2)) * hnn

/-! ## §III — the exact continuous classification -/

/-- **FIRST PRINCIPAL THEOREM OF TASK 15 (§III).**  For every unit spatial axis, the
continuous internal implementations of the inherited automorphism family are *exactly* the
central exponential–rotation multiples of the inherited reference implementation:

```
U θ = exp (α θ) [cos (β θ) 1 + sin (β θ) S] ⋆ Un n θ .
```

No exponential form was prescribed: it is derived from continuity, the group law, and the
exact centre. -/
theorem continuousAxisLift_classification {n : Vec3} (hn : IsUnitAxis n) (U : ℝ → W) :
    IsContinuousAxisLift n U ↔ ∃ α β : ℝ, ∀ θ, U θ = zexp α β θ ⋆ Un n θ := by
  constructor
  · rintro ⟨hU, hUc⟩
    obtain ⟨z, hz, hUz⟩ := (axisLift_iff hn U).1 hU
    obtain ⟨f, g, hfg, hzf⟩ := (centralHom_iff_coeffs z).1 hz
    have hUf : ∀ θ, U θ = zc (f θ) (g θ) ⋆ Un n θ := fun θ => by rw [hUz, hzf]
    have hUc0 : Continuous fun θ => U θ 0 := (continuous_apply 0).comp hUc
    have hUc1 : Continuous fun θ => U θ 1 := (continuous_apply 1).comp hUc
    have hUc2 : Continuous fun θ => U θ 2 := (continuous_apply 2).comp hUc
    have hUc3 : Continuous fun θ => U θ 3 := (continuous_apply 3).comp hUc
    have hUc4 : Continuous fun θ => U θ 4 := (continuous_apply 4).comp hUc
    have hUc5 : Continuous fun θ => U θ 5 := (continuous_apply 5).comp hUc
    have hUc6 : Continuous fun θ => U θ 6 := (continuous_apply 6).comp hUc
    have hUc7 : Continuous fun θ => U θ 7 := (continuous_apply 7).comp hUc
    have hrec : ∀ θ, f θ = Real.cos (θ / 2) * U θ 0
          - Real.sin (θ / 2) * (n.1 * U θ 6 - n.2.1 * U θ 5 + n.2.2 * U θ 4) ∧
        g θ = Real.cos (θ / 2) * U θ 7
          + Real.sin (θ / 2) * (n.1 * U θ 1 + n.2.1 * U θ 2 + n.2.2 * U θ 3) := by
      intro θ
      have h := residual_coeffs_of_coords hn (f θ) (g θ) θ
      rw [← hUf θ] at h
      exact h
    have hf : Continuous f := by
      have he : f = fun θ => Real.cos (θ / 2) * U θ 0
          - Real.sin (θ / 2) * (n.1 * U θ 6 - n.2.1 * U θ 5 + n.2.2 * U θ 4) :=
        funext fun θ => (hrec θ).1
      rw [he]; fun_prop
    have hg : Continuous g := by
      have he : g = fun θ => Real.cos (θ / 2) * U θ 7
          + Real.sin (θ / 2) * (n.1 * U θ 1 + n.2.1 * U θ 2 + n.2.2 * U θ 3) :=
        funext fun θ => (hrec θ).2
      rw [he]; fun_prop
    obtain ⟨α, β, hfe, hge⟩ :=
      coeff_continuous_classification hf hg hfg.f_add hfg.g_add hfg.f_zero hfg.g_zero
    exact ⟨α, β, fun θ => by rw [hUf, hfe, hge, zexp]⟩
  · rintro ⟨α, β, hU⟩
    have hUfun : U = fun θ => zexp α β θ ⋆ Un n θ := funext hU
    refine ⟨(axisLift_iff hn U).2 ⟨zexp α β, zexp_isCentralHom α β, hU⟩, ?_⟩
    rw [hUfun]
    exact continuous_zc_mul_Un n (by fun_prop) (by fun_prop)

/-- **PRINCIPAL THEOREM (§III), exact parameter count.**  The two real parameters of a
continuous axis lift are uniquely determined by the lift. -/
theorem continuousAxisLift_parameters_unique {n : Vec3} (hn : IsUnitAxis n)
    {α β α' β' : ℝ} (h : ∀ θ, zexp α β θ ⋆ Un n θ = zexp α' β' θ ⋆ Un n θ) :
    α = α' ∧ β = β' :=
  zexp_injective (α := α) (β := β) (α' := α') (β' := β')
    fun θ => Un_right_cancel hn (h θ)

end NullSectorTask15
