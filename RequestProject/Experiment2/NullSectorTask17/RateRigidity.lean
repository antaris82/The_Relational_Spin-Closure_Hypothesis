import RequestProject.Experiment2.NullSectorTask17.DomainGeometry

/-!
# Task 17, Package B: discrete-value rigidity on one local domain

This module isolates the exact local necessity statement for an **arbitrary** jointly
regular family that is exact transformation-valued on a set of unit directions, and then
uses the intrinsic geometry of Package A to decide whether the recovered discrete rate is
forced to be constant.

* §19–§22.  For an arbitrary set `D` of unit directions and an arbitrary jointly regular
  family exact on `D`, the two recovered coefficient functions satisfy `α n = 0` and
  `β n ∈ ℤ + 1/2` at every `n ∈ D`.  Only the inherited coincidence
  `PhiGen n (2π) = PhiGen n 0` is used, so no property of `D` beyond `D ⊆ unit directions`
  enters.
* §23, §24.  On a nonempty inherited domain `Dom v` the rate **is** constant.  The proof
  uses only the proved continuity of the recovered rate (Task 16) and the proved
  preconnectedness of `Dom v` (Package A), through the intermediate value property; no
  generic discreteness or local-constancy theorem is invoked.
* §25.  Constancy really needs the connectedness input: an explicit two-point domain
  carrying two *different* admissible labels is exhibited in Package D
  (`antipodal_pair_admissible`), so the hypothesis is not removable.
* §26, §27.  Existence and uniqueness of the single integer label of a local family.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## §19–§22 — the pointwise local necessity theorem on an arbitrary set -/

/-- **PRINCIPAL THEOREM (§19, §21, §22).**  Let `U` be jointly regular and exact
transformation-valued on an arbitrary set `D` of directions.  Then at every unit direction
of `D` the first recovered coefficient vanishes and the second lies in `ℤ + 1/2`.

Only the inherited closed relation `PhiGen n (2π) = PhiGen n 0` at the single direction `n`
is used; nothing about the shape of `D` is assumed. -/
theorem pointwise_rates {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {D : Set Vec3}
    (hV : IsTransformationValuedOn D U) {n : Vec3} (hn : n ∈ D) (hun : IsUnitAxis n) :
    rateAlpha U n = 0 ∧ ∃ k : ℤ, rateBeta U n = (k : ℝ) + 1 / 2 := by
  have hcoin : PhiGen n (2 * Real.pi) = PhiGen n 0 := by
    have h := coincidence_add_two_pi n 0
    rwa [zero_add] at h
  have h0 : U n 0 = w1 := (hU.lift n hun).unit
  have h2pi : U n (2 * Real.pi) = (1 : ℝ) • w1 := by
    rw [hV n hn n hn (2 * Real.pi) 0 hcoin, h0, one_smul]
  obtain ⟨hα, ⟨k, hk⟩, hcos⟩ :=
    full_turn_forces hU.toRegularFamily hun (ε := 1) (Or.inl rfl) h2pi
  refine ⟨hα, ?_⟩
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exfalso
    have hjr : rateBeta U n = (j : ℝ) := by rw [hk, hj]; push_cast; ring
    rw [hjr, Real.cos_int_mul_two_pi] at hcos
    norm_num at hcos
  · exact ⟨j, by rw [hk, hj]; push_cast; ring⟩

/-- **DERIVED (§20).**  The recovered coefficient functions of a jointly regular family
reproduce the family: this is the Task-16 joint-regularity classification, recorded here in
the form used below. -/
theorem recovered_form {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) :
    U n θ = zexp (rateAlpha U n) (rateBeta U n) θ ⋆ Un n θ :=
  regularFamily_param_spec hU.toRegularFamily hn θ

/-! ## §23, §24 — constancy of the discrete rate on an inherited domain -/

/-- **PRINCIPAL THEOREM (§23, §24).**  On a nonempty inherited domain the recovered
discrete rate of an exact jointly regular family is constant.  The only inputs are the
proved continuity of the rate and the proved preconnectedness of the domain. -/
theorem beta_const_on_Dom {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {v : Vec3}
    (hv : v ≠ 0) (hV : IsTransformationValuedOn (Dom v) U) :
    ∀ n ∈ Dom v, ∀ m ∈ Dom v, rateBeta U n = rateBeta U m := by
  have hcont : ContinuousOn (fun s : Sph => rateBeta U (s : Vec3)) (sphSet (Dom v)) :=
    (jointlyRegular_beta_continuous hU).continuousOn
  have hint : ∀ s ∈ sphSet (Dom v), ∃ k : ℤ, rateBeta U (s : Vec3) = (k : ℝ) + 1 / 2 := by
    intro s hs
    exact (pointwise_rates hU hV hs s.2).2
  have hconst := halfodd_const_of_preconnected (isPreconnected_sphSet_Dom hv) hcont hint
  intro n hn m hm
  exact hconst ⟨n, hn.1⟩ hn ⟨m, hm.1⟩ hm

/-! ## §26, §27 — the single integer label -/

/-- **PRINCIPAL THEOREM (§26).**  An exact jointly regular family on a nonempty inherited
domain carries a single integer label: the recovered coefficient functions are `α ≡ 0` and
`β ≡ k + 1/2` on the whole domain. -/
theorem exists_local_label {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {v : Vec3}
    (hv : v ≠ 0) (hV : IsTransformationValuedOn (Dom v) U) :
    ∃ k : ℤ, ∀ n ∈ Dom v, rateAlpha U n = 0 ∧ rateBeta U n = (k : ℝ) + 1 / 2 := by
  obtain ⟨n₀, hn₀⟩ := (Dom_nonempty_iff v).2 hv
  obtain ⟨k, hk⟩ := (pointwise_rates hU hV hn₀ hn₀.1).2
  refine ⟨k, fun n hn => ⟨(pointwise_rates hU hV hn hn.1).1, ?_⟩⟩
  rw [beta_const_on_Dom hU hv hV n hn n₀ hn₀, hk]

/-- **PRINCIPAL THEOREM (§27).**  The integer label is unique. -/
theorem local_label_unique {U : Vec3 → ℝ → W} {v : Vec3} (hv : v ≠ 0) {k l : ℤ}
    (hk : ∀ n ∈ Dom v, rateBeta U n = (k : ℝ) + 1 / 2)
    (hl : ∀ n ∈ Dom v, rateBeta U n = (l : ℝ) + 1 / 2) : k = l := by
  obtain ⟨n₀, hn₀⟩ := (Dom_nonempty_iff v).2 hv
  have h := (hk n₀ hn₀).symm.trans (hl n₀ hn₀)
  exact_mod_cast (by linarith : (k : ℝ) = (l : ℝ))

end NullSectorTask17
