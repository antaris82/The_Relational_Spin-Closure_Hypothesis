import RequestProject.Experiment2.NullSectorTask18.ReconstructionPredicates

/-!
# Task 18, Package D: the local-to-reference bridge, derived intrinsically

For an arbitrary jointly regular family `U` the *bridge* to the unique global sign-relaxed
reference `refFam` is **defined by the already derived relative-factor operation** (§26):

```
Bridge U n θ := ovl U refFam n θ .
```

No model formula for `U` is assumed anywhere in this definition (§27).  Everything else is
derived:

* §28.  `Bridge U n θ` is central at every unit direction.  Exactness is **not** needed for
  this; the honest hypothesis is joint regularity alone, and this is recorded.
* §29.  It is the **unique** element of the carrier implementing the comparison, under the
  inherited normalization of the two families.
* §30.  The exact carrier-level factorization `U n θ = Bridge U n θ ⋆ refFam n θ` holds at
  every unit direction and every parameter.
* §31.  The bridge rate is *recovered* from the already reconstructed central-rate
  functions: `Bridge U n θ = zexp 0 (rateBeta U n) θ` whenever the first recovered rate
  vanishes at `n`.  Nothing is assigned by hand.
* §32.  Exactness at a **single** direction already forces the bridge rate into `ℤ + 1/2`.
* §33.  On a preconnected exact domain the bridge factor is direction-independent and is
  determined by exactly one label `k + 1/2`.
* §34.  The classified integer overlap factor of two local exact families is the
  difference of their two bridge factors; the Task-17 integer transition theorem is
  **recovered** from this factorization rather than assumed.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## The reference rates -/

/-- **DERIVED.**  Both recovered rates of the global sign-relaxed reference vanish. -/
theorem refFam_rates {n : Vec3} (hn : IsUnitAxis n) :
    rateAlpha refFam n = 0 ∧ rateBeta refFam n = 0 := by
  rw [refFam_eq_famOf]
  exact (regular_family_arbitrary_parameters (fun _ => 0) (fun _ => 0)).2 n hn

/-! ## §26, §27 — the definition -/

/-- **NEUTRAL DEFINITION (§26).**  The relative factor of an arbitrary family to the unique
global sign-relaxed reference, defined by the already derived relative-factor operation.
No model formula for `U` enters (§27). -/
noncomputable def Bridge (U : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) : W := ovl U refFam n θ

theorem bridge_def (U : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) :
    Bridge U n θ = U n θ ⋆ refFam n (-θ) := rfl

/-! ## §28, §30 — centrality and the factorization -/

/-- **PRINCIPAL THEOREM (§28).**  The bridge is central at every unit direction.  Only
joint regularity of `U` is used: exactness is **not** required, and the statement is
recorded in this stronger form deliberately. -/
theorem bridge_central {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) : Bridge U n θ ∈ Z :=
  (ovl_central_and_factor hU refFam_jointlyRegular hn θ).1

/-- **PRINCIPAL THEOREM (§30).**  The exact carrier-level factorization of an arbitrary
jointly regular family through the global sign-relaxed reference. -/
theorem bridge_factorization {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) : U n θ = Bridge U n θ ⋆ refFam n θ :=
  (ovl_central_and_factor hU refFam_jointlyRegular hn θ).2

/-- **PRINCIPAL THEOREM (§29).**  Uniqueness of the bridge: any element of the carrier
implementing the comparison at a unit direction and a parameter is the bridge. -/
theorem bridge_unique {U : Vec3 → ℝ → W} {n : Vec3} (hn : IsUnitAxis n) {θ : ℝ} {c : W}
    (h : U n θ = c ⋆ refFam n θ) : c = Bridge U n θ :=
  ovl_unique refFam_jointlyRegular hn h

/-! ## §31 — the bridge rate, recovered -/

/-- **PRINCIPAL THEOREM (§31).**  The bridge is the inherited one-parameter central element
of the *already reconstructed* second rate of `U`.  The rate is recovered, not assigned. -/
theorem bridge_eq_zexp {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (hα : rateAlpha U n = 0) (θ : ℝ) :
    Bridge U n θ = zexp 0 (rateBeta U n) θ := by
  rw [Bridge, ovl_explicit hU refFam_jointlyRegular hn hα (refFam_rates hn).1 θ,
    (refFam_rates hn).2, sub_zero]

/-! ## §32 — exactness at one point forces a half-odd bridge rate -/

/-- **PRINCIPAL THEOREM (§32).**  Exactness at a **single** direction of the domain already
forces the bridge rate to lie in `ℤ + 1/2`; the vanishing of the first rate comes with
it. -/
theorem bridge_rate_halfOdd {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hexact : IsTransformationValuedOn D U) {n : Vec3} (hnD : n ∈ D)
    (hn : IsUnitAxis n) :
    IsHalfOdd (rateBeta U n) ∧ ∃ k : ℤ, ∀ θ : ℝ, Bridge U n θ = zexp 0 ((k : ℝ) + 1 / 2) θ := by
  obtain ⟨hα, k, hk⟩ := pointwise_rates hU hexact hnD hn
  refine ⟨⟨k, hk⟩, k, fun θ => ?_⟩
  rw [bridge_eq_zexp hU hn hα θ, hk]

/-! ## §33 — one label on a preconnected exact domain -/

/-- **PRINCIPAL THEOREM (§33).**  On a preconnected domain on which `U` is exact the bridge
does not depend on the direction, and it is given by exactly one half-odd label. -/
theorem bridge_direction_independent {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : UnitSet D) (hpre : PreconnDomain D)
    (hexact : IsTransformationValuedOn D U) :
    ∀ n ∈ D, ∀ m ∈ D, ∀ θ : ℝ, Bridge U n θ = Bridge U m θ := by
  intro n hn m hm θ
  have hαn := (pointwise_rates hU hexact hn (hunit n hn)).1
  have hαm := (pointwise_rates hU hexact hm (hunit m hm)).1
  rw [bridge_eq_zexp hU (hunit n hn) hαn θ, bridge_eq_zexp hU (hunit m hm) hαm θ,
    label_const_of_preconnected hU hunit hpre hexact n hn m hm]

/-- **PRINCIPAL THEOREM (§33), the unique label.**  On a nonempty preconnected exact domain
there is exactly one integer `k` with `Bridge U n θ = zexp 0 (k + 1/2) θ` for every
direction of the domain and every parameter. -/
theorem bridge_unique_label {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : UnitSet D) (hpre : PreconnDomain D)
    (hexact : IsTransformationValuedOn D U) {n₀ : Vec3} (hn₀ : n₀ ∈ D) :
    ∃! k : ℤ, ∀ n ∈ D, ∀ θ : ℝ, Bridge U n θ = zexp 0 ((k : ℝ) + 1 / 2) θ := by
  obtain ⟨-, k, hk⟩ := bridge_rate_halfOdd hU hexact hn₀ (hunit n₀ hn₀)
  refine ⟨k, fun n hn θ => ?_, fun l hl => ?_⟩
  · rw [bridge_direction_independent hU hunit hpre hexact n hn n₀ hn₀ θ, hk θ]
  · have h1 : ∀ θ : ℝ, zexp 0 ((l : ℝ) + 1 / 2) θ = zexp 0 ((k : ℝ) + 1 / 2) θ := by
      intro θ
      rw [← hl n₀ hn₀ θ, hk θ]
    have := (zexp_injective h1).2
    exact_mod_cast (by linarith : (l : ℝ) = (k : ℝ))

/-! ## §34 — the overlap factor is the difference of the two bridges -/

/-- **PRINCIPAL THEOREM (§34).**  The relative factor of two arbitrary jointly regular
families is exactly the difference of their two bridges: composing the first bridge with
the reversed second one gives the overlap.  Only associativity and the inherited one-axis
inverse law are used. -/
theorem overlap_eq_bridge_difference {U V : Vec3 → ℝ → W} (hV : IsJointlyRegularFamily V)
    {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    ovl U V n θ ⋆ Bridge V n θ = Bridge U n θ :=
  ovl_chain3 hV hn θ

/-- **PRINCIPAL THEOREM (§34), the recovered integer.**  For two families exact at a common
direction the overlap factor is the central one-parameter element of an **integer**, and
this is *derived from the bridge factorization*: the two bridge rates are half-odd, and
their difference is an integer.  The Task-17 integer transition theorem is recovered, not
assumed. -/
theorem integer_transition_from_bridges {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {DU DV : Set Vec3}
    (hexU : IsTransformationValuedOn DU U) (hexV : IsTransformationValuedOn DV V)
    {n : Vec3} (hnU : n ∈ DU) (hnV : n ∈ DV) (hn : IsUnitAxis n) :
    ∃ j : ℤ, ∀ θ : ℝ, ovl U V n θ = zexp 0 (j : ℝ) θ := by
  obtain ⟨-, kU, hkU⟩ := bridge_rate_halfOdd hU hexU hnU hn
  obtain ⟨-, kV, hkV⟩ := bridge_rate_halfOdd hV hexV hnV hn
  refine ⟨kU - kV, fun θ => ?_⟩
  have hstep : ovl U V n θ ⋆ zexp 0 ((kV : ℝ) + 1 / 2) θ = zexp 0 ((kU : ℝ) + 1 / 2) θ := by
    rw [← hkV θ, ← hkU θ]
    exact overlap_eq_bridge_difference hV hn θ
  have hcancel := congrArg (fun x : W => x ⋆ zexp 0 (-((kV : ℝ) + 1 / 2)) θ) hstep
  simp only [mul_assoc_W] at hcancel
  rw [zexp_zero_add, add_neg_cancel, zexp_zero_eq, mul_one_W, zexp_zero_add] at hcancel
  rw [hcancel]
  congr 1
  push_cast
  ring

end NullSectorTask18
