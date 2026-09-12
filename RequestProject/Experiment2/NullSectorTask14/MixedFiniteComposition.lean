import RequestProject.Experiment2.NullSectorTask14.MixedProjectors

/-!
# Task 14, Layer 8 (§24): mixed finite composition of the two axis automorphisms

Both orders are computed and the order dependence is **classified exactly**: a single
counterexample is not enough, so the complete set of parameter pairs at which the two
composites agree is determined.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## Degenerate parameters -/

theorem sin_eq_zero_of_cos_eq_one {θ : ℝ} (h : Real.cos θ = 1) : Real.sin θ = 0 := by
  have hpy := Real.sin_sq_add_cos_sq θ
  rw [h] at hpy
  have : Real.sin θ ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

theorem Phi_eq_id_of_cos_eq_one {θ : ℝ} (h : Real.cos θ = 1) : Phi θ = LinearMap.id := by
  have hs := sin_eq_zero_of_cos_eq_one h
  refine LinearMap.ext fun x => ?_
  funext i
  fin_cases i <;> simp [h, hs]

theorem PhiB_eq_id_of_cos_eq_one {φ : ℝ} (h : Real.cos φ = 1) :
    PhiB φ = LinearMap.id := by
  have hs := sin_eq_zero_of_cos_eq_one h
  refine LinearMap.ext fun x => ?_
  funext i
  fin_cases i <;> simp [h, hs]

/-! ## §24 — the two mixed composites -/

/-- **DERIVED (§24).**  The two mixed composites, evaluated on the first axis element. -/
theorem mixed_comp_wA (θ φ : ℝ) :
    (Phi θ) (PhiB φ wA)
      = Real.cos φ • wA + (Real.sin φ * Real.sin θ) • wB
        + (-(Real.sin φ * Real.cos θ)) • wC ∧
    (PhiB φ) (Phi θ wA) = Real.cos φ • wA + (-Real.sin φ) • wC := by
  constructor <;> · funext i; fin_cases i <;> simp [wA, wB, wC] <;> ring

/-- **DERIVED (§24).**  The two mixed composites, evaluated on the second axis element. -/
theorem mixed_comp_wB (θ φ : ℝ) :
    (Phi θ) (PhiB φ wB) = Real.cos θ • wB + Real.sin θ • wC ∧
    (PhiB φ) (Phi θ wB)
      = (Real.sin θ * Real.sin φ) • wA + Real.cos θ • wB
        + (Real.sin θ * Real.cos φ) • wC := by
  constructor <;> · funext i; fin_cases i <;> simp [wA, wB, wC] <;> ring

/-- **PRINCIPAL THEOREM (§24): `mixed_automorphisms_order_dependence`.**  The two mixed
composites of the independently reconstructed axis automorphisms agree **exactly** when
one of the two automorphisms is already trivial, or when both parameters are half-turns
(more precisely, when both sines vanish).  In every other case the composition is order
dependent. -/
theorem mixed_automorphisms_commute_iff (θ φ : ℝ) :
    (Phi θ).comp (PhiB φ) = (PhiB φ).comp (Phi θ) ↔
      (Real.sin θ = 0 ∧ Real.sin φ = 0) ∨ Real.cos θ = 1 ∨ Real.cos φ = 1 := by
  constructor
  · intro hcomm
    have hA : (Phi θ) (PhiB φ wA) = (PhiB φ) (Phi θ wA) := by
      have := congrArg (fun T : W →ₗ[ℝ] W => T wA) hcomm
      simpa using this
    have hB : (Phi θ) (PhiB φ wB) = (PhiB φ) (Phi θ wB) := by
      have := congrArg (fun T : W →ₗ[ℝ] W => T wB) hcomm
      simpa using this
    rw [(mixed_comp_wA θ φ).1, (mixed_comp_wA θ φ).2] at hA
    rw [(mixed_comp_wB θ φ).1, (mixed_comp_wB θ φ).2] at hB
    have e1 : Real.sin φ * Real.sin θ = 0 := by
      have := congrFun hA 2
      simpa [wA, wB, wC] using this
    have e2 : Real.sin φ * Real.cos θ = Real.sin φ := by
      have := congrFun hA 3
      simp [wA, wB, wC] at this
      linarith
    have e3 : Real.sin θ * Real.cos φ = Real.sin θ := by
      have := congrFun hB 3
      simp [wA, wB, wC] at this
      linarith
    by_cases hs : Real.sin θ = 0
    · by_cases hS : Real.sin φ = 0
      · exact Or.inl ⟨hs, hS⟩
      · refine Or.inr (Or.inl ?_)
        have : Real.sin φ * (Real.cos θ - 1) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hS
        · linarith
    · refine Or.inr (Or.inr ?_)
      have : Real.sin θ * (Real.cos φ - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hs
      · linarith
  · rintro (⟨hs, hS⟩ | hc | hC)
    · refine linMap_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        · simp only [LinearMap.comp_apply]
          funext i
          fin_cases i <;> simp [w1, wA, wB, wC, wP, wQ, wR, wS, hs, hS] <;> ring
    · rw [Phi_eq_id_of_cos_eq_one hc]
      rfl
    · rw [PhiB_eq_id_of_cos_eq_one hC]
      rfl

/-- **DERIVED (§24).**  An explicit order-dependent pair: the quarter-turn parameters.  The
classification above shows that this is the generic situation, not an isolated
accident. -/
theorem mixed_automorphisms_order_dependent_example :
    (Phi (Real.pi / 2)).comp (PhiB (Real.pi / 2))
      ≠ (PhiB (Real.pi / 2)).comp (Phi (Real.pi / 2)) := by
  intro hcon
  rcases (mixed_automorphisms_commute_iff _ _).1 hcon with ⟨hs, -⟩ | hc | hC
  · rw [Real.sin_pi_div_two] at hs; norm_num at hs
  · rw [Real.cos_pi_div_two] at hc; norm_num at hc
  · rw [Real.cos_pi_div_two] at hC; norm_num at hC

/-- **DERIVED (§24).**  Both half-turns *do* commute — the exceptional commuting pair
singled out by the classification.  This exact pair is used later in the coherence
audit. -/
theorem half_turns_commute :
    (Phi Real.pi).comp (PhiB Real.pi) = (PhiB Real.pi).comp (Phi Real.pi) := by
  refine (mixed_automorphisms_commute_iff _ _).2 (Or.inl ⟨?_, ?_⟩) <;> exact Real.sin_pi

end NullSectorTask14
