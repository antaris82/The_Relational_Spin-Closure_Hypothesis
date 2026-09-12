import RequestProject.Experiment2.NullSectorTask17.OverlapTransitions

/-!
# Task 17, Package F: reconstruction from local data

Question (§54): given a family of admissible local exact representatives whose overlap
factors satisfy every compatibility law derived in Package E, do they reconstruct a unique
global sign-relaxed family?

**Answer: no** — and the failure is not caused by a defect of the overlap data.

* Uniqueness always holds (§55, uniqueness half): two jointly regular families that agree
  on every member of a covering family of domains agree everywhere.
* Existence fails (§54, §56): the covering system `{locFam k on Dom v}` has *trivial*
  overlap factors — the strongest possible compatibility — covers every unit direction, and
  still no global sign-relaxed family restricts to it.  Indeed **no** family that is
  exact on some nonempty inherited domain is sign-relaxed, and conversely the unique global
  sign-relaxed family (the inherited reference family) is exact on **no** nonempty
  inherited domain.
* The missing datum is identified exactly (§56): it is the comparison across direction
  reversal.  A global rate function that is half-odd at every unit direction *and* odd
  under reversal cannot exist, while local systems on antipodal-free domains never see that
  relation.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## §55 — uniqueness of a reconstruction -/

/-- **PRINCIPAL THEOREM (§55), uniqueness.**  Two jointly regular families that agree on
every member of a covering family of domains agree at every unit direction and every
parameter.  A reconstruction, if it exists, is therefore unique. -/
theorem reconstruction_unique {ι : Type*} {D : ι → Set Vec3}
    (hcov : ∀ n : Vec3, IsUnitAxis n → ∃ i, n ∈ D i) {U V : Vec3 → ℝ → W}
    (h : ∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, U n θ = V n θ) :
    ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = V n θ := by
  intro n hn θ
  obtain ⟨i, hi⟩ := hcov n hn
  exact h i n hi θ

/-! ## Local exactness and the sign-relaxed class are incompatible -/

/-- **DERIVED.**  A local model is never sign-relaxed transformation-valued. -/
theorem locFam_not_signTransformationValued (k : ℤ) :
    ¬ IsSignTransformationValued (locFam k) := by
  intro hsign
  have hn : IsUnitAxis ((1, 0, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]
  have hzero : ∀ θ : ℝ, zexp 0 ((k : ℝ) + 1 / 2) θ = zexp 0 0 θ := by
    intro θ
    have heq := signValued_eq_reference (locFam_jointlyRegular k) hsign hn θ
    rw [locFam, refFam] at heq
    refine Un_right_cancel hn (θ := θ) ?_
    rw [heq, zexp_zero_eq, one_mul_W]
  have := (zexp_injective hzero).2
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-- **PRINCIPAL THEOREM (§54), the obstruction to reconstruction.**  A jointly regular
family that is exact on a nonempty inherited domain is never sign-relaxed
transformation-valued. -/
theorem exact_local_not_signTransformationValued {U : Vec3 → ℝ → W}
    (hU : IsJointlyRegularFamily U) {v : Vec3} (hv : v ≠ 0)
    (hexact : IsTransformationValuedOn (Dom v) U) : ¬ IsSignTransformationValued U := by
  intro hsign
  obtain ⟨k, hk⟩ := local_exact_eq_locFam hU hv hexact
  obtain ⟨n, hn⟩ := (Dom_nonempty_iff v).2 hv
  have hzero : ∀ θ : ℝ, zexp 0 ((k : ℝ) + 1 / 2) θ = zexp 0 0 θ := by
    intro θ
    have h1 := signValued_eq_reference hU hsign hn.1 θ
    have h2 := hk n hn θ
    rw [h2, locFam, refFam] at h1
    refine Un_right_cancel hn.1 (θ := θ) ?_
    rw [h1, zexp_zero_eq, one_mul_W]
  have := (zexp_injective hzero).2
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-- **DERIVED.**  Conversely, the unique global sign-relaxed family — the inherited
reference family — is exact on **no** nonempty inherited domain. -/
theorem refFam_not_exact_on_Dom {v : Vec3} (hv : v ≠ 0) :
    ¬ IsTransformationValuedOn (Dom v) refFam := by
  intro hexact
  obtain ⟨n, hn⟩ := (Dom_nonempty_iff v).2 hv
  obtain ⟨-, k, hk⟩ := pointwise_rates refFam_jointlyRegular hexact hn hn.1
  have hzero : rateBeta refFam n = 0 := by
    rw [refFam_eq_famOf]
    exact ((regular_family_arbitrary_parameters (fun _ => 0) (fun _ => 0)).2 n hn.1).2
  rw [hzero] at hk
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-! ## §54, §56 — the counterexample with perfectly compatible local data -/

/-- **PRINCIPAL THEOREM (§54, §56): REFUTATION.**  There is a covering system of exact
local representatives whose overlap data are as compatible as possible — every transition
factor is the unit — and which nevertheless reconstructs no global sign-relaxed family. -/
theorem local_data_do_not_reconstruct :
    ∃ F : Vec3 → Vec3 → ℝ → W,
      (∀ v : Vec3, IsJointlyRegularFamily (F v)) ∧
      (∀ v : Vec3, IsTransformationValuedOn (Dom v) (F v)) ∧
      (∀ n : Vec3, IsUnitAxis n → n ∈ Dom n) ∧
      (∀ (v w n : Vec3), IsUnitAxis n → ∀ θ : ℝ, ovl (F v) (F w) n θ = w1) ∧
      (∀ (v w : Vec3), ∀ n : Vec3, ∀ θ : ℝ, F v n θ = F w n θ) ∧
      ¬ ∃ G : Vec3 → ℝ → W, IsJointlyRegularFamily G ∧ IsSignTransformationValued G ∧
        ∀ v : Vec3, ∀ n ∈ Dom v, ∀ θ : ℝ, G n θ = F v n θ := by
  refine ⟨fun _ => locFam 0, fun v => locFam_jointlyRegular 0,
    fun v => locFam_transformationValuedOn 0 v, fun n hn => Dom_covers hn, ?_, fun v w n θ => rfl,
    ?_⟩
  · intro v w n hn θ
    exact ((locFam_jointlyRegular 0).lift n hn).mul_neg θ
  · rintro ⟨G, hG, hsign, hres⟩
    have hn : IsUnitAxis ((1, 0, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]
    have hexact : IsTransformationValuedOn (Dom (1, 0, 0)) G := by
      intro a ha b hb θ φ hP
      rw [hres _ a ha θ, hres _ b hb φ]
      exact locFam_transformationValuedOn 0 (1, 0, 0) a ha b hb θ φ hP
    have hv : ((1, 0, 0) : Vec3) ≠ 0 := by
      intro hcon
      have := congrArg (fun w : Vec3 => w.1) hcon
      norm_num at this
    exact exact_local_not_signTransformationValued hG hv hexact hsign

/-! ## §56 — the exact missing datum -/

/-- **PRINCIPAL THEOREM (§56).**  The datum that local exact systems cannot supply is the
comparison across direction reversal: no rate function is simultaneously continuous on the
unit directions, half-odd at every unit direction, and odd under reversal.  Local systems
live on antipodal-free domains and never encounter this relation. -/
theorem no_global_halfodd_odd_rate :
    ¬ ∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
      (∀ n : Vec3, IsUnitAxis n → ∃ k : ℤ, b n = (k : ℝ) + 1 / 2) ∧
      (∀ n : Vec3, IsUnitAxis n → b (-n) = -b n) := by
  rintro ⟨b, hcont, hhalf, hodd⟩
  have hjr : IsJointlyRegularFamily (famOf (fun _ => 0) b) :=
    jointlyRegular_famOf continuous_const hcont
  have hex : IsTransformationValuedOn {n : Vec3 | IsUnitAxis n} (famOf (fun _ => 0) b) :=
    famOfZ_exact_on (fun n hn => hn) (fun n hn => hhalf n hn) (fun n hn _ => hodd n hn)
  have hglob : IsTransformationValued (famOf (fun _ => 0) b) := by
    intro n m θ φ hn hm hP
    exact hex n hn m hm θ φ hP
  exact no_global_jointly_regular_transformationValued ⟨_, hjr, hglob⟩

end NullSectorTask17
