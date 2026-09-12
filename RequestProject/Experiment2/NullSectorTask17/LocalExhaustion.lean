import RequestProject.Experiment2.NullSectorTask17.RateRigidity

/-!
# Task 17, Package C: full exhaustion of the local families

Package B produced, for an exact jointly regular family on a nonempty inherited domain, a
single integer label.  This module upgrades the statement about *rates* to a statement
about *families*, and proves the converse, giving a genuine necessity-and-sufficiency
classification.

* §29.  Equality of the two recovered coefficient functions on a set of unit directions
  already forces equality of the internal families there, for **all** real transformation
  parameters (`eq_of_rates_eq`).
* §30, §31.  Local exactness plus joint regularity implies `U = locFam k` on the whole
  domain, for exactly one integer `k`.  The quantifiers are explicit: equality is asserted
  only for directions of the domain, and for every real parameter.
* §32.  Independently, every `locFam k` satisfies the local hypotheses: it is jointly
  regular and exactly transformation-valued on every inherited domain.
* §33.  The two directions are packaged as `local_family_classification`.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## §29 — equal rates give equal families -/

/-- **PRINCIPAL THEOREM (§29).**  Two jointly regular families whose recovered coefficient
functions agree at every direction of a set of unit directions agree there, for every real
transformation parameter. -/
theorem eq_of_rates_eq {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hrate : ∀ n ∈ D, rateAlpha U n = rateAlpha V n ∧ rateBeta U n = rateBeta V n) :
    ∀ n ∈ D, ∀ θ : ℝ, U n θ = V n θ := by
  intro n hn θ
  rw [recovered_form hU (hunit n hn) θ, recovered_form hV (hunit n hn) θ,
    (hrate n hn).1, (hrate n hn).2]

/-! ## §30, §31 — the exhaustion theorem -/

/-- **DERIVED.**  The recovered coefficient functions of the explicit local model. -/
theorem locFam_rateAlpha_beta (k : ℤ) {n : Vec3} (hn : IsUnitAxis n) :
    rateAlpha (locFam k) n = 0 ∧ rateBeta (locFam k) n = (k : ℝ) + 1 / 2 :=
  locFam_rates k hn

/-- **PRINCIPAL THEOREM (§30, §31).**  Local exactness and joint regularity force the
family to be one explicit local model on the whole inherited domain: there is an integer
`k` with `U n θ = locFam k n θ` for **every** unit direction `n` of the domain and
**every** real parameter `θ`. -/
theorem local_exact_eq_locFam {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {v : Vec3}
    (hv : v ≠ 0) (hexact : IsTransformationValuedOn (Dom v) U) :
    ∃ k : ℤ, ∀ n ∈ Dom v, ∀ θ : ℝ, U n θ = locFam k n θ := by
  obtain ⟨k, hk⟩ := exists_local_label hU hv hexact
  refine ⟨k, ?_⟩
  refine eq_of_rates_eq hU (locFam_jointlyRegular k) (fun n hn => hn.1) ?_
  intro n hn
  obtain ⟨ha, hb⟩ := locFam_rateAlpha_beta k hn.1
  exact ⟨by rw [(hk n hn).1, ha], by rw [(hk n hn).2, hb]⟩

/-- **DERIVED.**  Two distinct labels give distinct local models on a nonempty domain. -/
theorem locFam_injective_on_Dom {v : Vec3} (hv : v ≠ 0) {k l : ℤ}
    (h : ∀ n ∈ Dom v, ∀ θ : ℝ, locFam k n θ = locFam l n θ) : k = l := by
  obtain ⟨n₀, hn₀⟩ := (Dom_nonempty_iff v).2 hv
  have hz : ∀ θ : ℝ, zexp 0 ((k : ℝ) + 1 / 2) θ = zexp 0 ((l : ℝ) + 1 / 2) θ := by
    intro θ
    exact Un_right_cancel hn₀.1 (θ := θ) (h n₀ hn₀ θ)
  have := (zexp_injective hz).2
  exact_mod_cast (by linarith : (k : ℝ) = (l : ℝ))

/-- **PRINCIPAL THEOREM (§30), sharpened.**  The label is unique. -/
theorem local_exact_eq_locFam_unique {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {v : Vec3} (hv : v ≠ 0) (hexact : IsTransformationValuedOn (Dom v) U) :
    ∃! k : ℤ, ∀ n ∈ Dom v, ∀ θ : ℝ, U n θ = locFam k n θ := by
  obtain ⟨k, hk⟩ := local_exact_eq_locFam hU hv hexact
  refine ⟨k, hk, fun l hl => ?_⟩
  refine (locFam_injective_on_Dom hv (k := l) (l := k) ?_)
  intro n hn θ
  rw [← hl n hn θ, hk n hn θ]

/-! ## §32 — the converse: every local model is admissible -/

/-- **PRINCIPAL THEOREM (§32).**  Every explicit local model satisfies all the local
hypotheses, on every inherited domain: it is jointly regular and exactly
transformation-valued there.  This is proved independently of the necessity direction. -/
theorem locFam_local_hypotheses (k : ℤ) (v : Vec3) :
    IsJointlyRegularFamily (locFam k) ∧ IsTransformationValuedOn (Dom v) (locFam k) :=
  ⟨locFam_jointlyRegular k, locFam_transformationValuedOn k v⟩

/-! ## §33 — the classification theorem -/

/-- **PRINCIPAL THEOREM (§33): necessity and sufficiency.**  For a nonempty inherited
domain and a jointly regular family `U`, exact transformation-valuedness on the domain is
**equivalent** to `U` coinciding on that domain — for all unit directions of the domain and
all real parameters — with exactly one explicit local model `locFam k`. -/
theorem local_family_classification {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {v : Vec3} (hv : v ≠ 0) :
    IsTransformationValuedOn (Dom v) U ↔ ∃! k : ℤ, ∀ n ∈ Dom v, ∀ θ : ℝ,
      U n θ = locFam k n θ := by
  constructor
  · exact local_exact_eq_locFam_unique hU hv
  · rintro ⟨k, hk, -⟩
    intro n hn m hm θ φ hP
    rw [hk n hn θ, hk m hm φ]
    exact locFam_transformationValuedOn k v n hn m hm θ φ hP

end NullSectorTask17
