import RequestProject.Experiment2.NullSectorTask11.ReferenceExistence

/-!
# Task 11, Layer 5: the exact classification of all full lifts (§15, §16, §20)

The relative theorem of Layer 3 is now converted into an absolute one by
inserting the reference lift of Layer 4.  The result is

```
IsFullLift U  ↔  ∃ z, IsCentralHom z ∧ ∀ θ, U θ = z θ ⋆ Uref θ,
```

with the residual map taking values in the **exact center** — the derived
central two-plane — and satisfying exactly the multiplicative law derived in
§13.  This is the complete `ALGEBRAIC FREEDOM`; no continuity, boundedness,
periodicity or norm condition enters.

Section §16 (Conservation of Difficulty) is settled here as well: the Task-10
real scaling factor is proved to be exactly the intersection of this freedom
with the Task-10 two-plane `K`, hence a proper slice of a strictly larger
freedom.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## Coordinates of a residual map -/

/-- **COEFFICIENT FORM OF A RESIDUAL MAP.**  The pair of real coordinate
functions of a central-valued multiplicative map, in the derived basis `1, S`.
No further property is assumed. -/
structure IsCentralCoeffHom (f g : ℝ → ℝ) : Prop where
  /-- Normalization of the unit coefficient. -/
  f_zero : f 0 = 1
  /-- Normalization of the `S` coefficient. -/
  g_zero : g 0 = 0
  /-- Multiplicative law, unit coefficient. -/
  f_add : ∀ θ φ : ℝ, f (θ + φ) = f θ * f φ - g θ * g φ
  /-- Multiplicative law, `S` coefficient. -/
  g_add : ∀ θ φ : ℝ, g (θ + φ) = f θ * g φ + g θ * f φ

namespace IsCentralCoeffHom

variable {f g : ℝ → ℝ} (h : IsCentralCoeffHom f g)
include h

/-- The two coefficient functions never vanish simultaneously. -/
theorem sq_add_sq_pos (θ : ℝ) : 0 < f θ ^ 2 + g θ ^ 2 := by
  rcases lt_or_eq_of_le (by positivity : (0:ℝ) ≤ f θ ^ 2 + g θ ^ 2) with h' | h'
  · exact h'
  · exfalso
    have hf : f θ = 0 := by nlinarith [sq_nonneg (f θ), sq_nonneg (g θ)]
    have hg : g θ = 0 := by nlinarith [sq_nonneg (f θ), sq_nonneg (g θ)]
    have h1 := h.f_add θ (-θ)
    rw [add_neg_cancel, h.f_zero, hf, hg] at h1
    norm_num at h1

end IsCentralCoeffHom

/-- **DERIVED.**  A residual map is exactly a pair of real coefficient functions
obeying the two derived bilinear recursions. -/
theorem centralHom_iff_coeffs (z : ℝ → W) :
    IsCentralHom z ↔ ∃ f g : ℝ → ℝ, IsCentralCoeffHom f g ∧ ∀ θ, z θ = zc (f θ) (g θ) := by
  constructor
  · intro hz
    have hzc : ∀ θ, z θ = zc (z θ 0) (z θ 7) := by
      intro θ
      obtain ⟨a, b, hab⟩ := (mem_center_iff (z θ)).1 (hz.mem θ)
      rw [hab]; simp
    refine ⟨fun θ => z θ 0, fun θ => z θ 7, ⟨?_, ?_, ?_, ?_⟩, hzc⟩
    · rw [hz.unit]; simp [w1]
    · rw [hz.unit]; simp [w1]
    · intro θ φ
      have h := hz.mul θ φ
      rw [hzc θ, hzc φ, zc_mul_zc] at h
      have := congrFun h 0
      simpa using this
    · intro θ φ
      have h := hz.mul θ φ
      rw [hzc θ, hzc φ, zc_mul_zc] at h
      have := congrFun h 7
      simpa using this
  · rintro ⟨f, g, hfg, hz⟩
    refine ⟨fun θ => ?_, ?_, fun θ φ => ?_⟩
    · rw [hz]; exact (mem_center_iff _).2 ⟨_, _, rfl⟩
    · rw [hz, hfg.f_zero, hfg.g_zero, zc_one_zero]
    · rw [hz, hz, hz, zc_mul_zc, hfg.f_add, hfg.g_add]

/-! ## §15 — the exact classification of all full lifts -/

/-- **EXACT ALGEBRAIC LIFT CLASSIFICATION (§15).**  Every full-carrier internal
lift of the inherited algebra action is the reference lift multiplied by a
residual map with values in the exact center, and conversely.  Nothing is
normalized away. -/
theorem fullLift_classification (U : ℝ → W) :
    IsFullLift U ↔ ∃ z : ℝ → W, IsCentralHom z ∧ ∀ θ, U θ = z θ ⋆ Uref θ :=
  fullLift_relative_classification Uref_isFullLift U

/-- **EXACT ALGEBRAIC LIFT CLASSIFICATION, COEFFICIENT FORM.** -/
theorem fullLift_classification_coeffs (U : ℝ → W) :
    IsFullLift U ↔
      ∃ f g : ℝ → ℝ, IsCentralCoeffHom f g ∧ ∀ θ, U θ = zc (f θ) (g θ) ⋆ Uref θ := by
  rw [fullLift_classification]
  constructor
  · rintro ⟨z, hz, hU⟩
    obtain ⟨f, g, hfg, hzc⟩ := (centralHom_iff_coeffs z).1 hz
    exact ⟨f, g, hfg, fun θ => by rw [hU, hzc]⟩
  · rintro ⟨f, g, hfg, hU⟩
    exact ⟨fun θ => zc (f θ) (g θ), (centralHom_iff_coeffs _).2 ⟨f, g, hfg, fun _ => rfl⟩, hU⟩

/-! ## §16 — where the Task-10 real factor sits -/

/-- The product of a central element with an element of the Task-10 two-plane
`K`, in coordinates.  `S ⋆ R = -A` is the only new table entry used. -/
theorem zc_mul_ksc (a b c d : ℝ) :
    zc a b ⋆ ksc c d = ![a * c, -(b * d), 0, 0, 0, 0, a * d, b * c] := by
  funext i
  fin_cases i <;> simp [zc, ksc, w1, wS, wR]

@[simp] theorem zc_mul_ksc_coord_1 (a b c d : ℝ) : (zc a b ⋆ ksc c d) 1 = -(b * d) := by
  rw [zc_mul_ksc]; simp

@[simp] theorem zc_mul_ksc_coord_7 (a b c d : ℝ) : (zc a b ⋆ ksc c d) 7 = b * c := by
  rw [zc_mul_ksc]; simp

/-- **CONSERVATION OF DIFFICULTY (§16), one direction.**  If a full lift takes
its values in the Task-10 two-plane `K`, then its residual coefficient on the
derived central element `S` vanishes identically: the Task-10 freedom is the
intersection of the full central freedom with `K`. -/
theorem residual_S_coeff_eq_zero_of_mem_K {U : ℝ → W} {f g : ℝ → ℝ}
    (hU : ∀ θ, U θ = zc (f θ) (g θ) ⋆ Uref θ)
    (hK : ∀ θ, U θ ∈ K) (θ : ℝ) : g θ = 0 := by
  have h1 : U θ 1 = 0 := by
    have h := congrFun (eq_ksc_of_mem_K (hK θ)) 1
    simpa [ksc, w1, wR] using h
  have h7 : U θ 7 = 0 := by
    have h := congrFun (eq_ksc_of_mem_K (hK θ)) 7
    simpa [ksc, w1, wR] using h
  rw [hU θ, Uref_apply] at h1 h7
  rw [zc_mul_ksc_coord_1] at h1
  rw [zc_mul_ksc_coord_7] at h7
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  have h1' : g θ * Real.sin (θ / 2) = 0 := by linarith [h1]
  have key : g θ ^ 2 = (g θ * Real.sin (θ / 2)) * (g θ * Real.sin (θ / 2))
      + (g θ * Real.cos (θ / 2)) * (g θ * Real.cos (θ / 2)) := by
    linear_combination (-(g θ) ^ 2) * hpy
  rw [h1', h7] at key
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using key)

/-- **CONSERVATION OF DIFFICULTY (§16), converse direction.**  Conversely, a
residual map with vanishing `S` coefficient keeps the lift inside `K`, and there
it is exactly a real multiplicative rescaling of the reference lift. -/
theorem mem_K_of_residual_real {U : ℝ → W} {f g : ℝ → ℝ}
    (hU : ∀ θ, U θ = zc (f θ) (g θ) ⋆ Uref θ) (hg : ∀ θ, g θ = 0) (θ : ℝ) :
    U θ = f θ • Uref θ ∧ U θ ∈ K := by
  have hval : U θ = f θ • Uref θ := by
    rw [hU, hg, Uref_apply]
    rw [show zc (f θ) 0 = f θ • w1 from by simp [zc]]
    rw [smul_mul_W, one_mul_W]
  exact ⟨hval, by rw [hval, Uref_apply]; exact Submodule.smul_mem _ _ (ksc_mem_K _ _)⟩

/-- **THE TASK-10 LIFT PROBLEM IS EXACTLY THE `K`-SLICE OF THE FULL PROBLEM.** -/
theorem isKLift_iff (U : ℝ → W) : IsKLift U ↔ IsFullLift U ∧ ∀ θ, U θ ∈ K := by
  constructor
  · intro h; exact ⟨⟨h.unit, h.group, h.conj⟩, h.mem⟩
  · rintro ⟨h, hK⟩; exact ⟨hK, h.unit, h.group, h.conj⟩

/-- **THE FULL FREEDOM IS STRICTLY LARGER (§16).**  A full lift whose residual
map genuinely uses the derived central element `S` exists, and it leaves `K`. -/
theorem exists_fullLift_not_mem_K :
    ∃ U : ℝ → W, IsContinuousFullLift U ∧ ¬ (∀ θ, U θ ∈ K) := by
  have hcoeff : IsCentralCoeffHom Real.cos Real.sin :=
    ⟨Real.cos_zero, Real.sin_zero, Real.cos_add,
      fun θ φ => by rw [Real.sin_add]; ring⟩
  refine ⟨fun θ => zc (Real.cos θ) (Real.sin θ) ⋆ Uref θ, ⟨?_, ?_⟩, ?_⟩
  · exact (fullLift_classification_coeffs _).2 ⟨Real.cos, Real.sin, hcoeff, fun _ => rfl⟩
  · refine continuous_pi fun i => ?_
    have hc : Continuous fun θ : ℝ => (zc (Real.cos θ) (Real.sin θ) ⋆ Uref θ) i := by
      simp only [Uref_apply, zc_mul_ksc]
      fin_cases i <;> simp <;> fun_prop
    exact hc
  · intro hall
    have hg := residual_S_coeff_eq_zero_of_mem_K (f := Real.cos) (g := Real.sin)
      (fun _ => rfl) hall (Real.pi / 2)
    rw [Real.sin_pi_div_two] at hg
    norm_num at hg

end NullSectorTask11
