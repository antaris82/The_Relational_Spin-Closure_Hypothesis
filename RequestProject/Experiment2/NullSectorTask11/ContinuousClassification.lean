import RequestProject.Experiment2.NullSectorTask11.ExactLiftClassification

/-!
# Task 11, Layer 6: the continuous residual classification (§18, §19, §20)

This layer closes the principal unresolved obligation of Task 10.

The residual freedom of Layer 5 is an *arbitrary* multiplicative map with values
in the exact center.  Here every **continuous** such map is classified: there are
exactly **two** real continuous degrees of freedom, and the general continuous
residual map is

```
z θ = zc (exp (α θ) * cos (β θ)) (exp (α θ) * sin (β θ)),   α, β ∈ ℝ.
```

## Intrinsic character of the proof (§19)

The classification is carried out entirely in the derived real basis `1, S` of
the central plane: the two real coordinate functions `f, g` of `z` satisfy the
derived bilinear recursions, and the analysis is ordinary real analysis.  No
conventional complex-number identification is used and no result about complex
characters is imported.

## Analytic inputs, explicitly documented (§39)

* `intervalIntegral.integral_hasDerivAt_right` — differentiability of the
  primitive of a continuous function;
* `intervalIntegral.intervalIntegral_pos_of_pos_on`,
  `intervalIntegral.integral_comp_add_left`,
  `intervalIntegral.integral_interval_sub_left`, `intervalIntegral.integral_add`,
  `intervalIntegral.integral_sub`, `intervalIntegral.integral_const_mul` —
  elementary interval-integral calculus;
* `is_const_of_deriv_eq_zero` — a real function with vanishing derivative is
  constant;
* `HasDerivAt.exp`, `HasDerivAt.cos`, `HasDerivAt.sin`, `Real.sin_sq_add_cos_sq`,
  `Real.exp_add`, `Real.exp_ne_zero`, `Real.exp_eq_exp`.

## §20 — algebraic versus continuous

The algebraic classification of Layer 5 is *strictly* larger than the continuous
one; the two classes are kept separate and are never silently identified.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## Step 1 — a continuous solution of the recursions is differentiable -/

/-- **DERIVED (smoothing step).**  Continuity plus the two derived bilinear
recursions force differentiability.  The proof averages the family over a small
window and inverts the resulting constant central factor. -/
theorem coeff_differentiable {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfa : ∀ θ φ, f (θ + φ) = f θ * f φ - g θ * g φ)
    (hga : ∀ θ φ, g (θ + φ) = f θ * g φ + g θ * f φ)
    (hf0 : f 0 = 1) :
    Differentiable ℝ f ∧ Differentiable ℝ g := by
  have hev : ∀ᶠ s in nhds (0 : ℝ), (0 : ℝ) < f s :=
    Filter.Tendsto.eventually_const_lt (by rw [hf0]; norm_num) (hf.tendsto 0)
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 hev
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hwin : ∀ x ∈ Set.Ioo (0 : ℝ) δ, 0 < f x := by
    intro x hx
    refine hεf ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
    calc x < δ := hx.2
      _ < ε := by rw [hδdef]; linarith
  set c1 : ℝ := ∫ s in (0 : ℝ)..δ, f s with hc1def
  set c2 : ℝ := ∫ s in (0 : ℝ)..δ, g s with hc2def
  have hc1 : 0 < c1 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable 0 δ) hwin hδ
  set A : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, f s with hAdef
  set B : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, g s with hBdef
  have hA : ∀ x, HasDerivAt A (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hB : ∀ x, HasDerivAt B (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have hshift : ∀ θ : ℝ, (∫ s in (0 : ℝ)..δ, f (θ + s)) = A (θ + δ) - A θ := by
    intro θ
    rw [intervalIntegral.integral_comp_add_left f θ, add_zero, hAdef]
    exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  have hshiftg : ∀ θ : ℝ, (∫ s in (0 : ℝ)..δ, g (θ + s)) = B (θ + δ) - B θ := by
    intro θ
    rw [intervalIntegral.integral_comp_add_left g θ, add_zero, hBdef]
    exact (intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)).symm
  have hFf : ∀ θ : ℝ, f θ * c1 - g θ * c2 = A (θ + δ) - A θ := by
    intro θ
    rw [← hshift θ]
    have hfun : (fun s => f (θ + s)) = fun s => f θ * f s - g θ * g s := funext fun s => hfa θ s
    rw [show (∫ s in (0 : ℝ)..δ, f (θ + s)) = ∫ s in (0 : ℝ)..δ, (f θ * f s - g θ * g s) from by
      rw [hfun]]
    rw [intervalIntegral.integral_sub (f := fun s => f θ * f s) (g := fun s => g θ * g s)
        ((continuous_const.mul hf).intervalIntegrable _ _)
        ((continuous_const.mul hg).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hFg : ∀ θ : ℝ, f θ * c2 + g θ * c1 = B (θ + δ) - B θ := by
    intro θ
    rw [← hshiftg θ]
    have hfun : (fun s => g (θ + s)) = fun s => f θ * g s + g θ * f s := funext fun s => hga θ s
    rw [show (∫ s in (0 : ℝ)..δ, g (θ + s)) = ∫ s in (0 : ℝ)..δ, (f θ * g s + g θ * f s) from by
      rw [hfun]]
    rw [intervalIntegral.integral_add (f := fun s => f θ * g s) (g := fun s => g θ * f s)
        ((continuous_const.mul hg).intervalIntegrable _ _)
        ((continuous_const.mul hf).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hD : (0 : ℝ) < c1 ^ 2 + c2 ^ 2 := by positivity
  have hfeq : f = fun θ =>
      (c1 * (A (θ + δ) - A θ) + c2 * (B (θ + δ) - B θ)) / (c1 ^ 2 + c2 ^ 2) := by
    funext θ
    rw [← hFf θ, ← hFg θ]
    field_simp
    ring
  have hgeq : g = fun θ =>
      (c1 * (B (θ + δ) - B θ) - c2 * (A (θ + δ) - A θ)) / (c1 ^ 2 + c2 ^ 2) := by
    funext θ
    rw [← hFf θ, ← hFg θ]
    field_simp
    ring
  have hAd : Differentiable ℝ A := fun x => (hA x).differentiableAt
  have hBd : Differentiable ℝ B := fun x => (hB x).differentiableAt
  constructor
  · rw [hfeq]; fun_prop
  · rw [hgeq]; fun_prop

/-! ## Step 2 — the differential recursion -/

/-- **DERIVED.**  Differentiating the multiplicative law in the second argument
at zero turns the recursions into a linear differential system with the two real
constants `deriv f 0` and `deriv g 0`. -/
theorem coeff_hasDerivAt {f g : ℝ → ℝ} (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (hfa : ∀ θ φ, f (θ + φ) = f θ * f φ - g θ * g φ)
    (hga : ∀ θ φ, g (θ + φ) = f θ * g φ + g θ * f φ) (θ : ℝ) :
    HasDerivAt f (f θ * deriv f 0 - g θ * deriv g 0) θ ∧
      HasDerivAt g (f θ * deriv g 0 + g θ * deriv f 0) θ := by
  have hshiftf : HasDerivAt (fun φ => f (θ + φ)) (deriv f θ) 0 := by
    have h := ((hfd (θ + 0)).hasDerivAt).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
    simpa using h
  have hshiftg : HasDerivAt (fun φ => g (θ + φ)) (deriv g θ) 0 := by
    have h := ((hgd (θ + 0)).hasDerivAt).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
    simpa using h
  have hprodf : HasDerivAt (fun φ => f (θ + φ)) (f θ * deriv f 0 - g θ * deriv g 0) 0 := by
    have e : (fun φ => f (θ + φ)) = fun φ => f θ * f φ - g θ * g φ := funext (hfa θ)
    rw [e]
    exact (((hfd 0).hasDerivAt).const_mul (f θ)).sub (((hgd 0).hasDerivAt).const_mul (g θ))
  have hprodg : HasDerivAt (fun φ => g (θ + φ)) (f θ * deriv g 0 + g θ * deriv f 0) 0 := by
    have e : (fun φ => g (θ + φ)) = fun φ => f θ * g φ + g θ * f φ := funext (hga θ)
    rw [e]
    exact (((hgd 0).hasDerivAt).const_mul (f θ)).add (((hfd 0).hasDerivAt).const_mul (g θ))
  constructor
  · exact ((hfd θ).hasDerivAt).congr_deriv (hshiftf.unique hprodf)
  · exact ((hgd θ).hasDerivAt).congr_deriv (hshiftg.unique hprodg)

/-! ## Step 3 — the exact continuous solution -/

/-- **THE CONTINUOUS COEFFICIENT CLASSIFICATION.**  Every continuous solution of
the two derived recursions with the derived normalization is an exponential
times a rotation, with exactly two real constants. -/
theorem coeff_continuous_classification {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfa : ∀ θ φ, f (θ + φ) = f θ * f φ - g θ * g φ)
    (hga : ∀ θ φ, g (θ + φ) = f θ * g φ + g θ * f φ)
    (hf0 : f 0 = 1) (hg0 : g 0 = 0) :
    ∃ α β : ℝ, (∀ θ, f θ = Real.exp (α * θ) * Real.cos (β * θ)) ∧
      (∀ θ, g θ = Real.exp (α * θ) * Real.sin (β * θ)) := by
  obtain ⟨hfd, hgd⟩ := coeff_differentiable hf hg hfa hga hf0
  set α : ℝ := deriv f 0 with hαdef
  set β : ℝ := deriv g 0 with hβdef
  have hode : ∀ θ, HasDerivAt f (f θ * α - g θ * β) θ ∧
      HasDerivAt g (f θ * β + g θ * α) θ := fun θ => coeff_hasDerivAt hfd hgd hfa hga θ
  -- the two conserved quantities
  have hp : ∀ θ : ℝ, HasDerivAt
      (fun t => Real.exp (-(α * t)) * (Real.cos (β * t) * f t + Real.sin (β * t) * g t)) 0 θ := by
    intro θ
    have hb : HasDerivAt (fun t : ℝ => β * t) β θ := by
      simpa using (hasDerivAt_id θ).const_mul β
    have ha : HasDerivAt (fun t : ℝ => -(α * t)) (-α) θ := by
      simpa using ((hasDerivAt_id θ).const_mul α).neg
    have he := ha.exp
    have hc := hb.cos
    have hs := hb.sin
    exact (he.mul (((hc.mul (hode θ).1)).add ((hs.mul (hode θ).2)))).congr_deriv (by
      simp only [Pi.add_apply, Pi.mul_apply]; ring_nf)
  have hq : ∀ θ : ℝ, HasDerivAt
      (fun t => Real.exp (-(α * t)) * (Real.cos (β * t) * g t - Real.sin (β * t) * f t)) 0 θ := by
    intro θ
    have hb : HasDerivAt (fun t : ℝ => β * t) β θ := by
      simpa using (hasDerivAt_id θ).const_mul β
    have ha : HasDerivAt (fun t : ℝ => -(α * t)) (-α) θ := by
      simpa using ((hasDerivAt_id θ).const_mul α).neg
    have he := ha.exp
    have hc := hb.cos
    have hs := hb.sin
    exact (he.mul (((hc.mul (hode θ).2)).sub ((hs.mul (hode θ).1)))).congr_deriv (by
      simp only [Pi.sub_apply, Pi.mul_apply]; ring_nf)
  have hpconst := is_const_of_deriv_eq_zero (f := fun t =>
      Real.exp (-(α * t)) * (Real.cos (β * t) * f t + Real.sin (β * t) * g t))
    (fun x => (hp x).differentiableAt) (fun x => (hp x).deriv)
  have hqconst := is_const_of_deriv_eq_zero (f := fun t =>
      Real.exp (-(α * t)) * (Real.cos (β * t) * g t - Real.sin (β * t) * f t))
    (fun x => (hq x).differentiableAt) (fun x => (hq x).deriv)
  refine ⟨α, β, fun θ => ?_, fun θ => ?_⟩ <;>
  · have h1 := hpconst θ 0
    have h2 := hqconst θ 0
    simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, hf0, hg0,
      mul_one, add_zero, sub_zero] at h1 h2
    have hexp : Real.exp (-(α * θ)) * Real.exp (α * θ) = 1 := by
      rw [← Real.exp_add]; simp
    have hne : Real.exp (-(α * θ)) ≠ 0 := Real.exp_ne_zero _
    have A1 : Real.cos (β * θ) * f θ + Real.sin (β * θ) * g θ = Real.exp (α * θ) := by
      have := congrArg (fun t => Real.exp (α * θ) * t) h1
      simp only at this
      calc Real.cos (β * θ) * f θ + Real.sin (β * θ) * g θ
          = (Real.exp (-(α * θ)) * Real.exp (α * θ)) *
              (Real.cos (β * θ) * f θ + Real.sin (β * θ) * g θ) := by rw [hexp, one_mul]
        _ = Real.exp (α * θ) * (Real.exp (-(α * θ)) *
              (Real.cos (β * θ) * f θ + Real.sin (β * θ) * g θ)) := by ring
        _ = Real.exp (α * θ) := by rw [h1, mul_one]
    have A2 : Real.cos (β * θ) * g θ - Real.sin (β * θ) * f θ = 0 := by
      have := mul_eq_zero.1 (by rw [h2] : Real.exp (-(α * θ)) *
        (Real.cos (β * θ) * g θ - Real.sin (β * θ) * f θ) = 0)
      rcases this with h | h
      · exact absurd h hne
      · exact h
    have py := Real.sin_sq_add_cos_sq (β * θ)
    first
      | linear_combination Real.cos (β * θ) * A1 - Real.sin (β * θ) * A2 - f θ * py
      | linear_combination Real.sin (β * θ) * A1 + Real.cos (β * θ) * A2 - g θ * py

/-! ## Step 4 — the two parameters are unique -/

/-- **EXACT PARAMETER COUNT.**  The two real constants are uniquely determined by
the map, so the continuous residual freedom has exactly two real degrees of
freedom — no more and no fewer. -/
theorem coeff_parameters_unique {α β α' β' : ℝ}
    (h1 : ∀ θ : ℝ, Real.exp (α * θ) * Real.cos (β * θ)
      = Real.exp (α' * θ) * Real.cos (β' * θ))
    (h2 : ∀ θ : ℝ, Real.exp (α * θ) * Real.sin (β * θ)
      = Real.exp (α' * θ) * Real.sin (β' * θ)) :
    α = α' ∧ β = β' := by
  -- the squared modulus separates `α`
  have hmod : ∀ θ : ℝ, Real.exp (α * θ) = Real.exp (α' * θ) := by
    intro θ
    have e1 := h1 θ
    have e2 := h2 θ
    have py := Real.sin_sq_add_cos_sq (β * θ)
    have py' := Real.sin_sq_add_cos_sq (β' * θ)
    have hsq : Real.exp (α * θ) ^ 2 = Real.exp (α' * θ) ^ 2 := by
      linear_combination (Real.exp (α * θ) * Real.sin (β * θ)
            + Real.exp (α' * θ) * Real.sin (β' * θ)) * e2
        + (Real.exp (α * θ) * Real.cos (β * θ)
            + Real.exp (α' * θ) * Real.cos (β' * θ)) * e1
        - Real.exp (α * θ) ^ 2 * py + Real.exp (α' * θ) ^ 2 * py'
    have hpos : 0 < Real.exp (α * θ) := Real.exp_pos _
    have hpos' : 0 < Real.exp (α' * θ) := Real.exp_pos _
    nlinarith [hsq, hpos, hpos', sq_nonneg (Real.exp (α * θ) - Real.exp (α' * θ)),
      sq_nonneg (Real.exp (α * θ) + Real.exp (α' * θ))]
  have hα : α = α' := by
    have h := hmod 1
    rw [mul_one, mul_one, Real.exp_eq_exp] at h
    exact h
  subst hα
  refine ⟨rfl, ?_⟩
  -- with the moduli equal, the two rotations agree, and differentiating at zero
  -- separates `β`
  have hsin : ∀ θ : ℝ, Real.sin (β * θ) = Real.sin (β' * θ) := by
    intro θ
    have h := h2 θ
    have hne : Real.exp (α * θ) ≠ 0 := Real.exp_ne_zero _
    exact mul_left_cancel₀ hne h
  have hd1 : HasDerivAt (fun θ : ℝ => Real.sin (β * θ)) (Real.cos (β * 0) * β) 0 := by
    simpa using (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul β :
      HasDerivAt (fun t : ℝ => β * t) β 0).sin
  have hd2 : HasDerivAt (fun θ : ℝ => Real.sin (β * θ)) (Real.cos (β' * 0) * β') 0 := by
    have : (fun θ : ℝ => Real.sin (β * θ)) = fun θ : ℝ => Real.sin (β' * θ) := funext hsin
    rw [this]
    simpa using (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul β' :
      HasDerivAt (fun t : ℝ => β' * t) β' 0).sin
  have := hd1.unique hd2
  simpa using this

/-! ## Step 5 — the continuous residual maps, intrinsically -/

/-- **THE GENERAL CONTINUOUS RESIDUAL MAP**, written intrinsically in the derived
basis `1, S`.  Two real parameters. -/
noncomputable def zexp (α β θ : ℝ) : W :=
  zc (Real.exp (α * θ) * Real.cos (β * θ)) (Real.exp (α * θ) * Real.sin (β * θ))

@[simp] theorem zexp_zero (α β : ℝ) : zexp α β 0 = w1 := by
  simp [zexp]

theorem zexp_coeffs (α β : ℝ) :
    IsCentralCoeffHom (fun θ => Real.exp (α * θ) * Real.cos (β * θ))
      (fun θ => Real.exp (α * θ) * Real.sin (β * θ)) where
  f_zero := by simp
  g_zero := by simp
  f_add := by
    intro θ φ
    rw [show α * (θ + φ) = α * θ + α * φ from by ring, Real.exp_add,
      show β * (θ + φ) = β * θ + β * φ from by ring, Real.cos_add]
    ring
  g_add := by
    intro θ φ
    rw [show α * (θ + φ) = α * θ + α * φ from by ring, Real.exp_add,
      show β * (θ + φ) = β * θ + β * φ from by ring, Real.sin_add]
    ring

theorem zexp_isCentralHom (α β : ℝ) : IsCentralHom (zexp α β) :=
  (centralHom_iff_coeffs _).2 ⟨_, _, zexp_coeffs α β, fun _ => rfl⟩

/-- Continuity of a central-valued map is continuity of its two coefficients. -/
theorem continuous_zc {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun θ => zc (f θ) (g θ) := by
  simp only [zc]
  exact (hf.smul continuous_const).add (hg.smul continuous_const)

theorem zexp_continuous (α β : ℝ) : Continuous (zexp α β) := by
  refine continuous_zc ?_ ?_ <;> fun_prop

/-- **THE CONTINUOUS RESIDUAL CLASSIFICATION (§18).**  A residual map is
continuous exactly when it is the intrinsic exponential–rotation family, with two
real parameters. -/
theorem centralHom_continuous_classification (z : ℝ → W) :
    (IsCentralHom z ∧ Continuous z) ↔ ∃ α β : ℝ, ∀ θ, z θ = zexp α β θ := by
  constructor
  · rintro ⟨hz, hzc⟩
    obtain ⟨f, g, hfg, hzf⟩ := (centralHom_iff_coeffs z).1 hz
    have hf : Continuous f := by
      have : (fun θ => z θ 0) = f := by funext θ; rw [hzf]; simp
      rw [← this]; exact (continuous_apply 0).comp hzc
    have hg : Continuous g := by
      have : (fun θ => z θ 7) = g := by funext θ; rw [hzf]; simp
      rw [← this]; exact (continuous_apply 7).comp hzc
    obtain ⟨α, β, hfe, hge⟩ :=
      coeff_continuous_classification hf hg hfg.f_add hfg.g_add hfg.f_zero hfg.g_zero
    exact ⟨α, β, fun θ => by rw [hzf, hfe, hge, zexp]⟩
  · rintro ⟨α, β, hz⟩
    have he : z = zexp α β := funext hz
    rw [he]
    exact ⟨zexp_isCentralHom α β, zexp_continuous α β⟩

/-- **EXACT CONTINUOUS PARAMETER COUNT (§18).**  The two parameters are uniquely
determined: the continuous residual freedom has exactly two real degrees of
freedom. -/
theorem zexp_injective {α β α' β' : ℝ} (h : ∀ θ, zexp α β θ = zexp α' β' θ) :
    α = α' ∧ β = β' := by
  refine coeff_parameters_unique (α := α) (β := β) (α' := α') (β' := β') ?_ ?_
  · intro θ
    have := congrFun (h θ) 0
    simpa [zexp] using this
  · intro θ
    have := congrFun (h θ) 7
    simpa [zexp] using this

/-! ## Step 6 — the continuous full lifts -/

@[simp] theorem zc_mul_ksc_coord_0 (a b c d : ℝ) : (zc a b ⋆ ksc c d) 0 = a * c := by
  rw [zc_mul_ksc]; simp

@[simp] theorem zc_mul_ksc_coord_6 (a b c d : ℝ) : (zc a b ⋆ ksc c d) 6 = a * d := by
  rw [zc_mul_ksc]; simp

/-- **THE COMPLETE CONTINUOUS FULL-LIFT CLASSIFICATION (§18).**  Every continuous
full-carrier internal lift is the reference lift multiplied by the intrinsic
two-parameter exponential–rotation family, and conversely.  No normalization,
boundedness or periodicity is used. -/
theorem continuousFullLift_classification (U : ℝ → W) :
    IsContinuousFullLift U ↔ ∃ α β : ℝ, ∀ θ, U θ = zexp α β θ ⋆ Uref θ := by
  constructor
  · rintro ⟨hU, hUc⟩
    obtain ⟨f, g, hfg, hUf⟩ := (fullLift_classification_coeffs U).1 hU
    -- the two coefficients are continuous, because they are recovered from the
    -- coordinates of `U` by the inverse of the reference rotation
    have hcoord : ∀ θ, f θ = Real.cos (θ / 2) * U θ 0 - Real.sin (θ / 2) * U θ 6 ∧
        g θ = Real.cos (θ / 2) * U θ 7 + Real.sin (θ / 2) * U θ 1 := by
      intro θ
      have h := hUf θ
      rw [Uref_apply] at h
      have h0 : U θ 0 = f θ * Real.cos (θ / 2) := by rw [h, zc_mul_ksc_coord_0]
      have h6 : U θ 6 = f θ * -Real.sin (θ / 2) := by rw [h, zc_mul_ksc_coord_6]
      have h7 : U θ 7 = g θ * Real.cos (θ / 2) := by rw [h, zc_mul_ksc_coord_7]
      have h1 : U θ 1 = -(g θ * -Real.sin (θ / 2)) := by rw [h, zc_mul_ksc_coord_1]
      have hpy := Real.sin_sq_add_cos_sq (θ / 2)
      constructor
      · rw [h0, h6]; linear_combination (-(f θ)) * hpy
      · rw [h7, h1]; linear_combination (-(g θ)) * hpy
    have hUc0 : Continuous fun θ => U θ 0 := (continuous_apply 0).comp hUc
    have hUc1 : Continuous fun θ => U θ 1 := (continuous_apply 1).comp hUc
    have hUc6 : Continuous fun θ => U θ 6 := (continuous_apply 6).comp hUc
    have hUc7 : Continuous fun θ => U θ 7 := (continuous_apply 7).comp hUc
    have hf : Continuous f := by
      have he : f = fun θ => Real.cos (θ / 2) * U θ 0 - Real.sin (θ / 2) * U θ 6 :=
        funext fun θ => (hcoord θ).1
      rw [he]; fun_prop
    have hg : Continuous g := by
      have he : g = fun θ => Real.cos (θ / 2) * U θ 7 + Real.sin (θ / 2) * U θ 1 :=
        funext fun θ => (hcoord θ).2
      rw [he]; fun_prop
    obtain ⟨α, β, hfe, hge⟩ :=
      coeff_continuous_classification hf hg hfg.f_add hfg.g_add hfg.f_zero hfg.g_zero
    exact ⟨α, β, fun θ => by rw [hUf, hfe, hge, zexp]⟩
  · rintro ⟨α, β, hU⟩
    have hUfun : U = fun θ => zexp α β θ ⋆ Uref θ := funext hU
    constructor
    · exact (fullLift_classification U).2 ⟨zexp α β, zexp_isCentralHom α β, hU⟩
    · rw [hUfun]
      refine continuous_pi fun i => ?_
      have hexpand : ∀ θ : ℝ, zexp α β θ ⋆ Uref θ =
          ![Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2),
            -(Real.exp (α * θ) * Real.sin (β * θ) * -Real.sin (θ / 2)), 0, 0, 0, 0,
            Real.exp (α * θ) * Real.cos (β * θ) * -Real.sin (θ / 2),
            Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)] := by
        intro θ; rw [zexp, Uref_apply, zc_mul_ksc]
      simp only [hexpand]
      fin_cases i <;> simp <;> fun_prop

/-- **EXACT PARAMETER COUNT FOR LIFTS.**  Two continuous full lifts with the same
parameters coincide, and different parameters give different lifts. -/
theorem continuousFullLift_parameters_unique {α β α' β' : ℝ}
    (h : ∀ θ, zexp α β θ ⋆ Uref θ = zexp α' β' θ ⋆ Uref θ) : α = α' ∧ β = β' := by
  refine zexp_injective (α := α) (β := β) (α' := α') (β' := β') fun θ => ?_
  have hz := h θ
  have hcancel : ∀ x y : W, x ⋆ Uref θ = y ⋆ Uref θ → x = y := by
    intro x y hxy
    have h1 : (x ⋆ Uref θ) ⋆ Uref (-θ) = (y ⋆ Uref θ) ⋆ Uref (-θ) := by rw [hxy]
    rwa [mul_assoc_W, mul_assoc_W, Uref_isFullLift.mul_neg, mul_one_W, mul_one_W] at h1
  exact hcancel _ _ hz

/-! ## §20 — algebraic freedom is strictly larger than continuous freedom -/

/-- **DERIVED (§20).**  There is a *discontinuous* additive real function; the
construction uses only a complement of a one-dimensional `ℚ`-subspace of `ℝ`
(the axiom of choice enters exactly here, through
`Submodule.exists_isCompl`). -/
theorem exists_additive_not_linear :
    ∃ F : ℝ → ℝ, (∀ x y : ℝ, F (x + y) = F x + F y) ∧ ¬ ∃ c : ℝ, ∀ θ : ℝ, F θ = c * θ := by
  classical
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hs2 : Real.sqrt 2 ≠ 0 := by
    intro h
    exact hirr ⟨0, by simp [h]⟩
  set p : Submodule ℚ ℝ := Submodule.span ℚ {Real.sqrt 2} with hp
  obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
  have hmem : Real.sqrt 2 ∈ p := Submodule.mem_span_singleton_self _
  have hqne : q ≠ ⊥ := by
    intro hq
    have htop : p = ⊤ := by
      have := hpq.sup_eq_top
      rwa [hq, sup_bot_eq] at this
    have h1 : (1 : ℝ) ∈ p := htop ▸ Submodule.mem_top
    rw [hp, Submodule.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : (a : ℝ) * Real.sqrt 2 = 1 := by
      rw [← ha]; push_cast [Rat.smul_def]; ring
    have hane : (a : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at ha'
      norm_num at ha'
    refine hirr ⟨1 / a, ?_⟩
    push_cast
    rw [eq_comm, eq_div_iff hane]
    linear_combination ha'
  obtain ⟨y, hy, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hqne
  refine ⟨fun θ => ((p.linearProjOfIsCompl q hpq θ : ℝ)), fun x y => by simp, ?_⟩
  rintro ⟨c, hc⟩
  have h1 : ((p.linearProjOfIsCompl q hpq (Real.sqrt 2) : p) : ℝ) = Real.sqrt 2 := by
    rw [Submodule.linearProjOfIsCompl_apply_left hpq ⟨Real.sqrt 2, hmem⟩]
  have h2 : ((p.linearProjOfIsCompl q hpq y : p) : ℝ) = 0 := by
    rw [Submodule.linearProjOfIsCompl_apply_right hpq ⟨y, hy⟩]
    simp
  have hc1 := hc (Real.sqrt 2)
  have hc2 := hc y
  simp only [h1] at hc1
  simp only [h2] at hc2
  have hcv : c = 1 := by
    have hz : (c - 1) * Real.sqrt 2 = 0 := by linear_combination -hc1
    rcases mul_eq_zero.1 hz with h | h
    · linarith
    · exact absurd h hs2
  rw [hcv, one_mul] at hc2
  exact hyne hc2.symm

/-- **ALGEBRAIC ≠ CONTINUOUS (§20).**  There exists a residual map — hence a full
internal lift — which is algebraically admissible but is *not* a member of the
continuous family.  Discontinuous residual homomorphisms therefore really do
remain possible at the purely algebraic level, and the two classifications must
not be identified. -/
theorem exists_centralHom_not_continuous :
    ∃ z : ℝ → W, IsCentralHom z ∧ ¬ ∃ α β : ℝ, ∀ θ, z θ = zexp α β θ := by
  obtain ⟨F, hFadd, hFlin⟩ := exists_additive_not_linear
  refine ⟨fun θ => zc (Real.exp (F θ)) 0, ?_, ?_⟩
  · refine (centralHom_iff_coeffs _).2 ⟨fun θ => Real.exp (F θ), fun _ => 0, ⟨?_, rfl, ?_, ?_⟩,
      fun _ => rfl⟩
    · have : F 0 = 0 := by
        have := hFadd 0 0
        simp at this
        linarith
      rw [this, Real.exp_zero]
    · intro θ φ; rw [hFadd, Real.exp_add]; ring
    · intro θ φ; ring
  · rintro ⟨α, β, hz⟩
    have hcoord0 : ∀ θ, Real.exp (F θ) = Real.exp (α * θ) * Real.cos (β * θ) := by
      intro θ
      have := congrFun (hz θ) 0
      simpa [zexp] using this
    have hcoord7 : ∀ θ, (0 : ℝ) = Real.exp (α * θ) * Real.sin (β * θ) := by
      intro θ
      have := congrFun (hz θ) 7
      simpa [zexp] using this
    have hsin : ∀ θ, Real.sin (β * θ) = 0 := by
      intro θ
      rcases mul_eq_zero.1 (hcoord7 θ).symm with h | h
      · exact absurd h (Real.exp_ne_zero _)
      · exact h
    have hβ : β = 0 := by
      by_contra hne
      have := hsin (Real.pi / (2 * β))
      rw [show β * (Real.pi / (2 * β)) = Real.pi / 2 from by field_simp,
        Real.sin_pi_div_two] at this
      norm_num at this
    apply hFlin
    refine ⟨α, fun θ => ?_⟩
    have h := hcoord0 θ
    rw [hβ, zero_mul, Real.cos_zero, mul_one, Real.exp_eq_exp] at h
    exact h

end NullSectorTask11
