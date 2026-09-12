import RequestProject.Experiment2.NullSectorTask18.RegularityAudit

/-!
# Task 18, negative controls

Five controls, all proved, showing that the Task-18 statements are not accidentally weaker
or stronger than claimed, and in particular that nothing was quietly normalized away.

1. **Centrality of the bridge does not need exactness, but half-oddness does.**  An
   explicit jointly regular family has a central bridge whose rate is `1/3`, which is not
   half-odd.  So §32 genuinely uses exactness.
2. **Direction-independence of the bridge genuinely needs preconnectedness.**  An explicit
   family which *is* exact on a (disconnected) admissible domain has bridges with two
   different rates at two directions of that domain.
3. **Bridge-normalization is not innocuous.**  The normalized family — the global
   sign-relaxed reference — is exactly transformation-valued on no nonempty inherited
   domain.  The conversion factor really is carrying the exactness.
4. **The conversion factor is nontrivial.**  The bridge of the explicit local model is not
   the unit of the carrier.
5. **Nothing is quotiented.**  The retained bridge determines the family completely: two
   jointly regular families with the same bridge at a unit direction are equal there.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## Control 1 — exactness is what makes the bridge rate half-odd -/

/-- **NEGATIVE CONTROL 1.**  A jointly regular family whose bridge is central at every unit
direction but whose bridge rate is `1/3`, hence not half-odd.  Centrality holds without
exactness; half-oddness does not. -/
theorem bridge_central_but_not_halfOdd :
    ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧
      (∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, Bridge U n θ ∈ Z) ∧
      (∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, Bridge U n θ = zexp 0 (1 / 3) θ) ∧
      ¬ IsHalfOdd (1 / 3 : ℝ) := by
  set U : Vec3 → ℝ → W := famOf (fun _ => 0) (fun _ => 1 / 3) with hU
  have hjr : IsJointlyRegularFamily U := jointlyRegular_famOf continuous_const continuous_const
  have hrates : ∀ n : Vec3, IsUnitAxis n → rateAlpha U n = 0 ∧ rateBeta U n = 1 / 3 :=
    fun n hn => (regular_family_arbitrary_parameters (fun _ => 0) (fun _ => 1 / 3)).2 n hn
  refine ⟨U, hjr, fun n hn θ => bridge_central hjr hn θ, fun n hn θ => ?_, ?_⟩
  · rw [bridge_eq_zexp hjr hn (hrates n hn).1 θ, (hrates n hn).2]
  · rintro ⟨k, hk⟩
    have h6 : (6 * k : ℤ) = -1 := by
      have : (6 * (k : ℝ)) = -1 := by linarith
      exact_mod_cast this
    omega

/-! ## Control 2 — preconnectedness is what makes the bridge direction-independent -/

/-- **NEGATIVE CONTROL 2.**  An exact jointly regular representative on a (disconnected)
admissible domain whose bridge rate takes two different values inside that domain.  So the
direction-independence of §33 genuinely uses preconnectedness. -/
theorem bridge_direction_dependent :
    ∃ (U : Vec3 → ℝ → W) (D : Set Vec3), IsJointlyRegularFamily U ∧
      IsTransformationValuedOn D U ∧ e1 ∈ D ∧ p35 ∈ D ∧
      (∀ θ : ℝ, Bridge U e1 θ = zexp 0 (5 / 2) θ) ∧
      (∀ θ : ℝ, Bridge U p35 θ = zexp 0 (3 / 2) θ) := by
  obtain ⟨-, m1, -, m3, -, U, hU, hex, h1, -, h3', -⟩ := multiD_admissible_four_labels
  have hα : ∀ n ∈ multiD, rateAlpha U n = 0 := fun n hn =>
    (pointwise_rates hU hex hn hn.1).1
  refine ⟨U, multiD, hU, hex, m1, m3, fun θ => ?_, fun θ => ?_⟩
  · rw [bridge_eq_zexp hU e1_isUnitAxis (hα e1 m1) θ, h1]
  · rw [bridge_eq_zexp hU p35_isUnitAxis (hα p35 m3) θ, h3']

/-! ## Control 3 — normalization moves the exactness into the retained factor -/

/-- **NEGATIVE CONTROL 3.**  The bridge-normalized family is the global sign-relaxed
reference, and that family is exactly transformation-valued on **no** nonempty inherited
domain.  Bridge-normalization therefore does not preserve exactness: the exactness is
carried by the retained conversion factor. -/
theorem normalization_does_not_preserve_exactness {v : Vec3} (hv : v ≠ 0) :
    (∀ n ∈ Dom v, ∀ θ : ℝ, bridgeNormalize (locFam 0) n θ = refFam n θ) ∧
      ¬ IsTransformationValuedOn (Dom v) refFam :=
  ⟨fun _ hn θ => bridgeNormalize_eq_refFam (locFam_jointlyRegular 0) hn.1 θ,
    refFam_not_exact_on_Dom hv⟩

/-! ## Control 4 — the conversion factor is not the unit -/

theorem w1_eq_zc : (w1 : W) = zc 1 0 := by rw [zc]; module

/-- **NEGATIVE CONTROL 4.**  The bridge of the explicit local model is a nontrivial central
element: at the parameter `π` it is not the unit of the carrier. -/
theorem bridge_locFam_ne_one : Bridge (locFam 0) e1 Real.pi ≠ w1 := by
  have hα : rateAlpha (locFam 0) e1 = 0 := (locFam_rates 0 e1_isUnitAxis).1
  have hβ : rateBeta (locFam 0) e1 = 1 / 2 := by
    have := (locFam_rates 0 e1_isUnitAxis).2
    rw [this]; norm_num
  have hval : Bridge (locFam 0) e1 Real.pi = zc 0 1 := by
    rw [bridge_eq_zexp (locFam_jointlyRegular 0) e1_isUnitAxis hα Real.pi, hβ, zexp_zero_val,
      show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [hval, w1_eq_zc]
  intro hcon
  have := (zc_injective hcon).1
  norm_num at this

/-! ## Control 5 — nothing is quotiented -/

/-- **NEGATIVE CONTROL 5.**  The retained conversion factor determines the local family
completely: two jointly regular families with the same bridge at a unit direction coincide
there.  No information is lost by carrying the factor explicitly, and none is quotiented
away. -/
theorem bridge_determines_family {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {n : Vec3} (hn : IsUnitAxis n) {θ : ℝ}
    (h : Bridge U n θ = Bridge V n θ) : U n θ = V n θ := by
  rw [bridge_factorization hU hn θ, bridge_factorization hV hn θ, h]

end NullSectorTask18
