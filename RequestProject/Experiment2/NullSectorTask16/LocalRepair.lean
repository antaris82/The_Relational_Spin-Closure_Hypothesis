import RequestProject.Experiment2.NullSectorTask16.RegularDefect

/-!
# Task 16, Layer 5 (Work Package 5): the minimal local repair

Work Package 3 proved that global jointly regular transformation-valued closure is
impossible.  This layer determines the weakest repair supported by the inherited algebra.

Nothing is added by name: the only new object is a *proper domain of directions*, namely
the set of unit directions on which the inherited spatial form against a fixed unit
direction is positive,

```
Dom v = { n : IsUnitAxis n ∧ 0 < h n v } .
```

The results are

* **local existence** — on every such domain a jointly regular family exists which is
  *exactly* transformation-valued there (`locFam_transformationValuedOn`);
* **coverage** — every unit direction lies in such a domain (`Dom_covers`);
* **local classification** — a jointly regular family transformation-valued on a domain
  must have first central rate zero and second central rate in `ℤ + 1/2` at every
  direction of the domain (`local_rates`); these are exactly the families `locFam k`;
* **overlap** — two local choices differ by a factor which is central, invertible,
  *independent of the direction*, and uniquely determined (`locFam_overlap`,
  `locFam_overlap_unique`, `overlap_defect_central`);
* **chains** — the overlap data of a finite chain of domains compose, and the composite is
  the direct transition, so no additional datum is needed for finite chains
  (`locFam_overlap_chain`);
* **the failure is not local** — the same formula is *not* transformation-valued globally
  (`locFam_not_global`).

Status: **GLOBAL CHOICE IMPOSSIBLE; LOCAL CHOICES EXIST AND REQUIRE CENTRAL TRANSITION
DATA**, the transition class being the discrete family indexed by `ℤ`.
-/

namespace NullSectorTask16

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15

/-! ## Proper domains of directions -/

/-- **NEUTRAL DEFINITION.**  The domain of unit directions attached to a direction `v`:
those unit directions whose inherited spatial form against `v` is positive.  Only the
inherited form is used. -/
def Dom (v : Vec3) : Set Vec3 := {n : Vec3 | IsUnitAxis n ∧ 0 < h3 n v}

theorem mem_Dom_isUnitAxis {v n : Vec3} (h : n ∈ Dom v) : IsUnitAxis n := h.1

/-- **DERIVED.**  Every unit direction lies in its own domain: the domains cover all unit
directions. -/
theorem Dom_covers {n : Vec3} (hn : IsUnitAxis n) : n ∈ Dom n :=
  ⟨hn, by rw [show h3 n n = 1 from hn]; norm_num⟩

/-- **DERIVED.**  A domain contains no pair of opposite directions: the antipodal
identification of the coincidence relation is invisible inside one domain. -/
theorem Dom_no_antipodal {v n : Vec3} (h : n ∈ Dom v) : -n ∉ Dom v := by
  rintro ⟨-, hpos⟩
  have hneg : h3 (-n) v = -h3 n v := by
    simp only [h3, dot3_apply, Prod.fst_neg, Prod.snd_neg]; ring
  rw [hneg] at hpos
  linarith [h.2]

/-- **DERIVED (the key domain property).**  Inside one domain a scalar proportion between
two directions forces the two scalars to be equal — the sign ambiguity that obstructs the
global problem is absent. -/
theorem Dom_scalar_eq {v n m : Vec3} (hn : n ∈ Dom v) (hm : m ∈ Dom v) {s u : ℝ}
    (h : s • n = u • m) : s = u := by
  have hsq := unit_smul_sq hn.1 hm.1 h
  have hpair : s * h3 n v = u * h3 m v := by
    have := congrArg (fun w : Vec3 => h3 w v) h
    simpa only [h3, dot3_smul_left] using this
  rcases mul_eq_zero.1 (by linear_combination hsq : (s - u) * (s + u) = 0) with h' | h'
  · linarith
  · have hu : u = -s := by linarith
    rw [hu] at hpair
    have hs0 : s * (h3 n v + h3 m v) = 0 := by linarith [hpair]
    have hpos : 0 < h3 n v + h3 m v := by linarith [hn.2, hm.2]
    have hs : s = 0 := by
      rcases mul_eq_zero.1 hs0 with h'' | h''
      · exact h''
      · linarith
    rw [hs] at hu ⊢
    linarith

/-! ## Transformation-valuedness relative to a domain -/

/-- **NEUTRAL DEFINITION (Work Package 5).**  A family is transformation-valued *on a
domain* when equal inherited automorphisms coming from directions of that domain receive
equal internal representatives. -/
def IsTransformationValuedOn (D : Set Vec3) (U : Vec3 → ℝ → W) : Prop :=
  ∀ n ∈ D, ∀ m ∈ D, ∀ θ φ : ℝ, PhiGen n θ = PhiGen m φ → U n θ = U m φ

/-! ## Parameter shifts along a coincidence branch -/

theorem zexp_zero_val (b θ : ℝ) : zexp 0 b θ = zc (Real.cos (b * θ)) (Real.sin (b * θ)) := by
  simp [zexp]

theorem zc_smul (e a b : ℝ) : e • zc a b = zc (e * a) (e * b) := by
  rw [zc, zc]; module

/-- **DERIVED.**  The two branches of the coincidence relation correspond to the two
possible parameter shifts. -/
theorem param_shift {θ φ ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : Real.cos (θ / 2) = ε * Real.cos (φ / 2))
    (hs : Real.sin (θ / 2) = ε * Real.sin (φ / 2)) :
    ∃ j : ℤ, (ε = 1 ∧ θ = φ + 4 * Real.pi * j) ∨
      (ε = -1 ∧ θ = φ + 2 * Real.pi + 4 * Real.pi * j) := by
  have hpy := Real.sin_sq_add_cos_sq (φ / 2)
  rcases hε with rfl | rfl
  · have hcos : Real.cos (θ / 2 - φ / 2) = 1 := by
      rw [Real.cos_sub, hc, hs]; linarith
    obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 hcos
    exact ⟨j, Or.inl ⟨rfl, by linarith [hj]⟩⟩
  · have hcos : Real.cos (θ / 2 - φ / 2 - Real.pi) = 1 := by
      rw [show θ / 2 - φ / 2 - Real.pi = (θ / 2 - φ / 2) + -Real.pi by ring, Real.cos_add,
        Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi, Real.cos_sub, Real.sin_sub,
        hc, hs]
      linarith
    obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 hcos
    exact ⟨j, Or.inr ⟨rfl, by linarith [hj]⟩⟩

/-- **DERIVED.**  A half-odd central rate transports the central factor with exactly the
branch sign.  This is the algebraic reason why the half-odd rates repair the local
problem. -/
theorem zexp_half_odd_smul (k : ℤ) {θ φ ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : Real.cos (θ / 2) = ε * Real.cos (φ / 2))
    (hs : Real.sin (θ / 2) = ε * Real.sin (φ / 2)) :
    zexp 0 ((k : ℝ) + 1 / 2) θ = ε • zexp 0 ((k : ℝ) + 1 / 2) φ := by
  obtain ⟨j, hj⟩ := param_shift hε hc hs
  rw [zexp_zero_val, zexp_zero_val, zc_smul]
  rcases hj with ⟨rfl, hθ⟩ | ⟨rfl, hθ⟩
  · have harg : ((k : ℝ) + 1 / 2) * θ
        = ((k : ℝ) + 1 / 2) * φ + ((2 * j * k + j : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hθ]; push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    congr 1 <;> ring
  · have harg : ((k : ℝ) + 1 / 2) * θ
        = (((k : ℝ) + 1 / 2) * φ + Real.pi) + ((2 * j * k + j + k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hθ]; push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, Real.cos_add_pi,
      Real.sin_add_pi]
    congr 1 <;> ring

/-- **DERIVED.**  A branch of the coincidence relation transports the reference
implementations with the branch sign. -/
theorem Un_smul_of_branch {n m : Vec3} {θ φ ε : ℝ}
    (hc : Real.cos (θ / 2) = ε * Real.cos (φ / 2))
    (hs : Real.sin (θ / 2) • n = (ε * Real.sin (φ / 2)) • m) :
    Un n θ = ε • Un m φ := by
  have hJ : Real.sin (θ / 2) • Jmap n = (ε * Real.sin (φ / 2)) • Jmap m := by
    rw [← Jmap_linear.2, hs, Jmap_linear.2]
  rw [Un, Un, hc, hJ]
  module

/-! ## The local families -/

/-- **NEUTRAL DEFINITION.**  The local family attached to an integer label. -/
noncomputable def locFam (k : ℤ) (n : Vec3) (θ : ℝ) : W :=
  zexp 0 ((k : ℝ) + 1 / 2) θ ⋆ Un n θ

theorem locFam_eq_famOf (k : ℤ) :
    locFam k = famOf (fun _ => 0) (fun _ => (k : ℝ) + 1 / 2) := rfl

/-- **DERIVED.**  Every local family is jointly regular. -/
theorem locFam_jointlyRegular (k : ℤ) : IsJointlyRegularFamily (locFam k) := by
  rw [locFam_eq_famOf]
  exact jointlyRegular_famOf continuous_const continuous_const

theorem locFam_rates (k : ℤ) {n : Vec3} (hn : IsUnitAxis n) :
    rateAlpha (locFam k) n = 0 ∧ rateBeta (locFam k) n = (k : ℝ) + 1 / 2 := by
  obtain ⟨h1, h2⟩ := regularFamily_param_unique (locFam_jointlyRegular k).toRegularFamily hn
    (α := 0) (β := (k : ℝ) + 1 / 2) (fun _ => rfl)
  exact ⟨h1.symm, h2.symm⟩

/-! ## Work Package 5 — local existence -/

/-- **PRINCIPAL THEOREM (Work Package 5), local existence.**  On every proper domain of
directions each local family is *exactly* transformation-valued: equal inherited
automorphisms of directions of the domain receive equal internal representatives, with no
sign relaxation. -/
theorem locFam_transformationValuedOn (k : ℤ) (v : Vec3) :
    IsTransformationValuedOn (Dom v) (locFam k) := by
  intro n hn m hm θ φ hP
  obtain ⟨ε, hε, hc, hsv⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      Real.cos (θ / 2) = ε * Real.cos (φ / 2) ∧
      Real.sin (θ / 2) • n = (ε * Real.sin (φ / 2)) • m := by
    rcases (coincidence_iff_coords hn.1 hm.1 θ φ).1 hP with ⟨hc, hs⟩ | ⟨hc, hs⟩
    · exact ⟨1, Or.inl rfl, by linarith, by simpa using hs⟩
    · refine ⟨-1, Or.inr rfl, by linarith, ?_⟩
      rw [hs]; module
  have hsc : Real.sin (θ / 2) = ε * Real.sin (φ / 2) := Dom_scalar_eq hn hm hsv
  have hUn : Un n θ = ε • Un m φ := Un_smul_of_branch hc hsv
  have hz : zexp 0 ((k : ℝ) + 1 / 2) θ = ε • zexp 0 ((k : ℝ) + 1 / 2) φ :=
    zexp_half_odd_smul k hε hc hsc
  rw [locFam, locFam, hz, hUn, smul_mul_W, mul_smul_W, smul_smul]
  have hee : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hee, one_smul]

/-- **DERIVED.**  The very same formula is *not* transformation-valued globally: local
repair does not repair the global problem. -/
theorem locFam_not_global (k : ℤ) : ¬ IsTransformationValued (locFam k) := by
  intro hV
  exact no_global_jointly_regular_transformationValued ⟨locFam k, locFam_jointlyRegular k, hV⟩

/-! ## Work Package 5 — local classification -/

/-- **PRINCIPAL THEOREM (Work Package 5), local necessity.**  A jointly regular family that
is transformation-valued on a proper domain has vanishing first central rate and second
central rate in `ℤ + 1/2` at every direction of the domain.  Hence the local families
`locFam k` exhaust the admissible local choices, direction by direction. -/
theorem local_rates {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {v : Vec3}
    (hV : IsTransformationValuedOn (Dom v) U) {n : Vec3} (hn : n ∈ Dom v) :
    rateAlpha U n = 0 ∧ ∃ k : ℤ, rateBeta U n = (k : ℝ) + 1 / 2 := by
  have hcoin : PhiGen n (2 * Real.pi) = PhiGen n 0 := by
    have h := coincidence_add_two_pi n 0
    rwa [zero_add] at h
  have h0 : U n 0 = w1 := (hU.lift n hn.1).unit
  have h2pi : U n (2 * Real.pi) = (1 : ℝ) • w1 := by
    rw [hV n hn n hn (2 * Real.pi) 0 hcoin, h0, one_smul]
  obtain ⟨hα, ⟨k, hk⟩, hcos⟩ :=
    full_turn_forces hU.toRegularFamily hn.1 (ε := 1) (Or.inl rfl) h2pi
  refine ⟨hα, ?_⟩
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exfalso
    have hjr : rateBeta U n = (j : ℝ) := by
      rw [hk, hj]; push_cast; ring
    rw [hjr, show (j : ℝ) * (2 * Real.pi) = (j : ℝ) * (2 * Real.pi) from rfl,
      Real.cos_int_mul_two_pi] at hcos
    norm_num at hcos
  · exact ⟨j, by rw [hk, hj]; push_cast; ring⟩

/-! ## Work Package 5 — the overlap data -/

/-- **PRINCIPAL THEOREM (Work Package 5), overlap.**  Two local choices differ by a factor
which is central, invertible, and *independent of the direction*: it depends only on the
parameter and on the two integer labels. -/
theorem locFam_overlap (k l : ℤ) (n : Vec3) (θ : ℝ) :
    locFam k n θ = zexp 0 ((k : ℝ) - l) θ ⋆ locFam l n θ ∧
      zexp 0 ((k : ℝ) - l) θ ∈ Z ∧ IsCentralUnit (zexp 0 ((k : ℝ) - l) θ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [locFam, locFam, ← mul_assoc_W, zexp_zero_add,
      show (k : ℝ) - l + ((l : ℝ) + 1 / 2) = (k : ℝ) + 1 / 2 by ring]
  · rw [zexp_zero_val]; exact zc_mem_Z _ _
  · rw [zexp_zero_val]
    refine isCentralUnit_zc ?_
    have := Real.sin_sq_add_cos_sq (((k : ℝ) - l) * θ)
    intro hcon
    nlinarith [this, hcon]

/-- **PRINCIPAL THEOREM (Work Package 5), uniqueness of the overlap datum.**  The
transition factor between two local choices is uniquely determined: no residual freedom
survives in it. -/
theorem locFam_overlap_unique {k l : ℤ} {n : Vec3} (hn : IsUnitAxis n) {θ : ℝ} {c : W}
    (h : locFam k n θ = c ⋆ locFam l n θ) : c = zexp 0 ((k : ℝ) - l) θ := by
  have hfac := (locFam_overlap k l n θ).1
  have heq : c ⋆ locFam l n θ = zexp 0 ((k : ℝ) - l) θ ⋆ locFam l n θ := by rw [← h, hfac]
  refine Un_right_cancel hn (θ := θ) ?_
  have hz : ∀ d : W, d ⋆ locFam l n θ
      = (d ⋆ zexp 0 ((l : ℝ) + 1 / 2) θ) ⋆ Un n θ := by
    intro d; rw [locFam, mul_assoc_W]
  rw [hz, hz] at heq
  have hcan := Un_right_cancel hn heq
  have hinv : zexp 0 ((l : ℝ) + 1 / 2) θ ⋆ zexp 0 ((l : ℝ) + 1 / 2) (-θ) = w1 := by
    have h1 := (zexp_isCentralHom 0 ((l : ℝ) + 1 / 2)).mul θ (-θ)
    rw [add_neg_cancel, (zexp_isCentralHom 0 ((l : ℝ) + 1 / 2)).unit] at h1
    exact h1.symm
  have := congrArg (fun t : W => t ⋆ zexp 0 ((l : ℝ) + 1 / 2) (-θ)) hcan
  simp only [mul_assoc_W, hinv, mul_one_W] at this
  rw [this]

/-- **PRINCIPAL THEOREM (Work Package 5), chain consistency.**  The overlap data of a
finite chain of local choices compose to the direct transition.  This follows from the
inherited product alone; no additional datum is required for finite chains. -/
theorem locFam_overlap_chain (k l m : ℤ) (θ : ℝ) :
    zexp 0 ((k : ℝ) - l) θ ⋆ zexp 0 ((l : ℝ) - m) θ = zexp 0 ((k : ℝ) - m) θ := by
  rw [zexp_zero_add, show (k : ℝ) - l + ((l : ℝ) - m) = (k : ℝ) - m by ring]

/-- **DERIVED (Work Package 5), generality of the overlap statement.**  For *any* two
regular families the discrepancy on a common direction is a central unit; centrality of the
overlap datum is therefore not special to the explicit local choices. -/
theorem overlap_defect_central {U V : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsRegularFamily V) {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    (U n θ ⋆ V n (-θ)) ∈ Z ∧ U n θ = (U n θ ⋆ V n (-θ)) ⋆ V n θ := by
  have hiU := (hU n hn).1.implements θ
  have hiV := (hV n hn).1.implements θ
  refine ⟨implements_defect_mem_Z hiU hiV, ?_⟩
  rw [mul_assoc_W, (hV n hn).1.neg_mul θ, mul_one_W]

/-! ## Work Package 5 — the status -/

/-- **PRINCIPAL THEOREM (Work Package 5): the exact status.**  Global exact closure is
impossible; local exact closure exists on domains that cover every unit direction; the
difference between two local choices is a central unit independent of the direction and
uniquely determined; and finite chains of such differences compose. -/
theorem local_repair_status :
    (¬ ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U) ∧
    (∀ v : Vec3, IsJointlyRegularFamily (locFam 0) ∧
      IsTransformationValuedOn (Dom v) (locFam 0)) ∧
    (∀ n : Vec3, IsUnitAxis n → n ∈ Dom n) ∧
    (∀ (k l : ℤ) (n : Vec3) (θ : ℝ), locFam k n θ = zexp 0 ((k : ℝ) - l) θ ⋆ locFam l n θ ∧
      IsCentralUnit (zexp 0 ((k : ℝ) - l) θ)) ∧
    (∀ (k l m : ℤ) (θ : ℝ),
      zexp 0 ((k : ℝ) - l) θ ⋆ zexp 0 ((l : ℝ) - m) θ = zexp 0 ((k : ℝ) - m) θ) :=
  ⟨no_global_jointly_regular_transformationValued,
    fun v => ⟨locFam_jointlyRegular 0, locFam_transformationValuedOn 0 v⟩,
    fun _ hn => Dom_covers hn,
    fun k l n θ => ⟨(locFam_overlap k l n θ).1, (locFam_overlap k l n θ).2.2⟩,
    locFam_overlap_chain⟩

end NullSectorTask16
