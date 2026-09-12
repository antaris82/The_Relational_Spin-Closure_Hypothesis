import RequestProject.Experiment2.NullSectorTask17.LocalExhaustion

/-!
# Task 17, Package D: classification of admissible direction domains

The exact local representative problem is stated here for an **arbitrary** set `D` of unit
directions — no openness, connectedness, or Task-16 shape is assumed in advance (§35, §36).

Results:

* §37.  The complete list of conditions forced on the recovered coefficient functions of an
  exact jointly regular family on `D`: `α = 0` on `D`, `β ∈ ℤ + 1/2` on `D`, `β` continuous
  on all unit directions, and `β(-n) = -β(n)` for every antipodal pair *inside* `D`.
* §38.  Containing an antipodal pair is **not** an obstruction: an explicit two-point
  domain `{n, -n}` is admissible, carrying the two opposite labels.
* §39.  Absence of antipodal pairs **is** sufficient: on every antipodal-free set of unit
  directions each explicit local model is exactly transformation-valued.
* §40.  Hence no further necessary condition beyond the (possible) antipodal compatibility
  is needed; the exact criterion is packaged as `admissible_iff_exists_rate_function`.
* §41.  Connectedness changes the classification of the local label: on a preconnected
  domain the label is unique, whereas the disconnected two-point domain of §38 carries two
  different labels simultaneously.
* §42.  **Refuted**: not every admissible connected open domain is contained in an
  inherited `Dom v`.  An explicit admissible, open, path-connected domain `YDom` is
  constructed which is contained in no `Dom v`.
* §43.  The inherited domains are **not** maximal among admissible domains: an explicit
  strictly larger admissible domain is exhibited.  (No order-theoretic superlative is
  claimed for them anywhere.)
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## §35, §36 — the exact local representative problem on an arbitrary set -/

/-- **NEUTRAL DEFINITION (§36).**  A set of directions is *admissible* when it consists of
unit directions and carries an exact local representative: a jointly regular family which
is exactly transformation-valued on it.  Nothing about openness, connectedness or the
Task-16 shape is required. -/
def IsAdmissibleDomain (D : Set Vec3) : Prop :=
  (∀ n ∈ D, IsUnitAxis n) ∧
    ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValuedOn D U

/-- **NEUTRAL DEFINITION.**  A set of directions contains no antipodal pair. -/
def AntipodalFree (D : Set Vec3) : Prop := ∀ n ∈ D, -n ∉ D

/-! ## Exactness criterion for the explicit central families -/

theorem famOfZ_apply (b : Vec3 → ℝ) (n : Vec3) (θ : ℝ) :
    famOf (fun _ => 0) b n θ = zexp 0 (b n) θ ⋆ Un n θ := rfl

theorem zexp_zero_neg (c φ : ℝ) : zexp 0 (-c) φ = zexp 0 c (-φ) := by
  rw [zexp, zexp, show (0 : ℝ) * φ = 0 * (-φ) by ring,
    show -c * φ = c * (-φ) by ring]

/-- **DERIVED.**  Along one direction, a half-odd central rate transports the whole family
with the branch sign; hence the two representatives of a branch-related pair agree. -/
theorem famOfZ_branch_eq {b : Vec3 → ℝ} {n : Vec3} {k : ℤ} (hb : b n = (k : ℝ) + 1 / 2)
    {θ φ ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : Real.cos (θ / 2) = ε * Real.cos (φ / 2))
    (hs : Real.sin (θ / 2) = ε * Real.sin (φ / 2)) :
    famOf (fun _ => 0) b n θ = famOf (fun _ => 0) b n φ := by
  have hUn : Un n θ = ε • Un n φ := by
    refine Un_smul_of_branch hc ?_
    rw [hs]
  have hz : zexp 0 (b n) θ = ε • zexp 0 (b n) φ := by
    rw [hb]; exact zexp_half_odd_smul k hε hc hs
  have hee : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [famOfZ_apply, famOfZ_apply, hz, hUn, smul_mul_W, mul_smul_W, smul_smul, hee, one_smul]

/-- **DERIVED.**  At a parameter where the reference implementation is central, a half-odd
central rate returns the unit exactly. -/
theorem famOfZ_at_sin_zero {b : Vec3 → ℝ} {n : Vec3} {k : ℤ} (hb : b n = (k : ℝ) + 1 / 2)
    {θ : ℝ} (hs : Real.sin (θ / 2) = 0) : famOf (fun _ => 0) b n θ = w1 := by
  obtain ⟨a, ha⟩ := Real.sin_eq_zero_iff.1 hs
  have hc2 : Real.cos (θ / 2) * Real.cos (θ / 2) = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2), hs]
  have hUn : Un n θ = Real.cos (θ / 2) • w1 := by
    rw [Un, hs, zero_smul, sub_zero]
  have hθ : θ = 2 * ((a : ℝ) * Real.pi) := by linarith [ha]
  have harg : b n * θ = θ / 2 + ((k * a : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hb, hθ]; push_cast; ring
  have hzc : zexp 0 (b n) θ = Real.cos (θ / 2) • w1 := by
    rw [zexp]
    simp only [zero_mul, Real.exp_zero, one_mul]
    rw [harg, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, hs, zc]
    module
  rw [famOfZ_apply, hzc, hUn, smul_mul_W, mul_smul_W, one_mul_W, smul_smul, hc2, one_smul]

/-- **PRINCIPAL THEOREM (§39, §40), sufficiency.**  Let `b` be any rate function which is
half-odd at every direction of `D` and odd on every antipodal pair contained in `D`.  Then
the associated jointly regular family is *exactly* transformation-valued on `D`.  No
openness, connectedness or shape assumption on `D` is used. -/
theorem famOfZ_exact_on {b : Vec3 → ℝ} {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hhalf : ∀ n ∈ D, ∃ k : ℤ, b n = (k : ℝ) + 1 / 2)
    (hodd : ∀ n ∈ D, -n ∈ D → b (-n) = -b n) :
    IsTransformationValuedOn D (famOf (fun _ => 0) b) := by
  intro n hn m hm θ φ hP
  obtain ⟨kn, hkn⟩ := hhalf n hn
  obtain ⟨km, hkm⟩ := hhalf m hm
  have hnu := hunit n hn
  have hmu := hunit m hm
  obtain ⟨ε, hε, hc, hsv⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      Real.cos (θ / 2) = ε * Real.cos (φ / 2) ∧
      Real.sin (θ / 2) • n = (ε * Real.sin (φ / 2)) • m := by
    rcases (coincidence_iff_coords hnu hmu θ φ).1 hP with ⟨hc, hs⟩ | ⟨hc, hs⟩
    · exact ⟨1, Or.inl rfl, by linarith, by simpa using hs⟩
    · refine ⟨-1, Or.inr rfl, by linarith, ?_⟩
      rw [hs]; module
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  by_cases hs0 : Real.sin (θ / 2) = 0
  · have hsm : Real.sin (φ / 2) = 0 := by
      have h0 : (ε * Real.sin (φ / 2)) • m = 0 := by rw [← hsv, hs0, zero_smul]
      have hz := smul_unit_eq_zero hmu h0
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hεne
      · exact h
    rw [famOfZ_at_sin_zero hkn hs0, famOfZ_at_sin_zero hkm hsm]
  · have hsq := unit_smul_sq hnu hmu hsv
    have hnm := unit_eq_of_smul hs0 hsv
    set r : ℝ := (ε * Real.sin (φ / 2)) / Real.sin (θ / 2) with hr
    have hr2 : r * r = 1 := by
      rw [hr]
      field_simp
      nlinarith [hsq]
    have hcase : r = 1 ∨ r = -1 := by
      rcases mul_eq_zero.1 (by linear_combination hr2 : (r - 1) * (r + 1) = 0) with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcase with hr1 | hr1
    · -- the two directions coincide
      have hnmeq : n = m := by rw [hnm, hr1, one_smul]
      subst hnmeq
      have hss : Real.sin (θ / 2) = ε * Real.sin (φ / 2) := smul_unit_inj hnu hsv
      exact famOfZ_branch_eq hkn hε hc hss
    · -- the two directions are opposite
      have hnmeq : m = -n := by
        rw [hnm, hr1]
        module
      have hnegD : -n ∈ D := by rw [← hnmeq]; exact hm
      have hbm : b m = -b n := by rw [hnmeq]; exact hodd n hn hnegD
      have hss : Real.sin (θ / 2) = ε * Real.sin ((-φ) / 2) := by
        have hsv' : Real.sin (θ / 2) • n = (-(ε * Real.sin (φ / 2))) • n := by
          rw [hsv, hnmeq]; module
        have := smul_unit_inj hnu hsv'
        rw [show (-φ) / 2 = -(φ / 2) by ring, Real.sin_neg]
        linarith [this]
      have hcc : Real.cos (θ / 2) = ε * Real.cos ((-φ) / 2) := by
        rw [show (-φ) / 2 = -(φ / 2) by ring, Real.cos_neg]
        exact hc
      have hstep := famOfZ_branch_eq (b := b) (n := n) hkn hε hcc hss
      have hmφ : famOf (fun _ => 0) b m φ = famOf (fun _ => 0) b n (-φ) := by
        rw [famOfZ_apply, famOfZ_apply, hbm, zexp_zero_neg, hnmeq, Un_neg_axis]
      rw [hmφ, hstep]

/-! ## §37 — the necessary conditions -/

/-- **PRINCIPAL THEOREM (§37).**  Exact transformation-valuedness on an arbitrary set of
unit directions, together with joint regularity, forces exactly the following: the first
recovered rate vanishes on `D`, the second is half-odd on `D`, the second is continuous on
all unit directions, and the second is odd on every antipodal pair contained in `D`. -/
theorem admissible_necessary {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n) (hexact : IsTransformationValuedOn D U) :
    (∀ n ∈ D, rateAlpha U n = 0) ∧
      (∀ n ∈ D, ∃ k : ℤ, rateBeta U n = (k : ℝ) + 1 / 2) ∧
      (Continuous fun s : Sph => rateBeta U (s : Vec3)) ∧
      (∀ n ∈ D, -n ∈ D → rateBeta U (-n) = -rateBeta U n) := by
  refine ⟨fun n hn => (pointwise_rates hU hexact hn (hunit n hn)).1,
    fun n hn => (pointwise_rates hU hexact hn (hunit n hn)).2,
    jointlyRegular_beta_continuous hU, ?_⟩
  intro n hn hneg
  have hnu := hunit n hn
  have hnnu : IsUnitAxis (-n) := isUnitAxis_neg hnu
  have hα := (pointwise_rates hU hexact hn hnu).1
  have hαn := (pointwise_rates hU hexact hneg hnnu).1
  have hkey : ∀ θ : ℝ, zexp 0 (rateBeta U n) θ = zexp 0 (-rateBeta U (-n)) θ := by
    intro θ
    have hP : PhiGen n θ = PhiGen (-n) (-θ) := by
      rw [coincidence_neg_axis n (-θ), neg_neg]
    have heq := hexact n hn (-n) hneg θ (-θ) hP
    have h1 := recovered_form hU hnu θ
    have h2 := recovered_form hU hnnu (-θ)
    have hUn : Un (-n) (-θ) = Un n θ := by rw [Un_neg_axis, neg_neg]
    rw [h1, h2, hα, hαn, hUn] at heq
    have hcan := Un_right_cancel hnu (θ := θ) heq
    rw [hcan, zexp_zero_neg]
  have := (zexp_injective hkey).2
  linarith

/-! ## §38 — an antipodal pair is not an obstruction -/

theorem h3_neg_self {n : Vec3} (hn : IsUnitAxis n) : h3 (-n) n = -1 := by
  have : h3 n n = 1 := hn
  rw [h3_neg_left, this]

/-- **PRINCIPAL THEOREM (§38): REFUTATION.**  Containing an antipodal pair is *not* an
obstruction to exact local representability.  For every unit direction the two-point set
`{n, -n}` is admissible; the exact representative carries the two opposite labels `1/2` at
`n` and `-1/2` at `-n`. -/
theorem antipodal_pair_admissible {n : Vec3} (hn : IsUnitAxis n) :
    IsAdmissibleDomain ({n, -n} : Set Vec3) ∧
      ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧
        IsTransformationValuedOn ({n, -n} : Set Vec3) U ∧
        rateBeta U n = 1 / 2 ∧ rateBeta U (-n) = -(1 / 2) := by
  classical
  set b : Vec3 → ℝ := fun m => (1 / 2) * h3 m n with hb
  have hnn : h3 n n = 1 := hn
  have hbn : b n = 1 / 2 := by
    have hval : b n = 1 / 2 * h3 n n := rfl
    rw [hval, hnn]; ring
  have hbneg : b (-n) = -(1 / 2) := by
    have hval : b (-n) = 1 / 2 * h3 (-n) n := rfl
    rw [hval, h3_neg_self hn]; ring
  have hnnu : IsUnitAxis (-n) := isUnitAxis_neg hn
  have hunit : ∀ m ∈ ({n, -n} : Set Vec3), IsUnitAxis m := by
    rintro m (rfl | rfl)
    · exact hn
    · exact hnnu
  have hhalf : ∀ m ∈ ({n, -n} : Set Vec3), ∃ k : ℤ, b m = (k : ℝ) + 1 / 2 := by
    rintro m (rfl | rfl)
    · exact ⟨0, by rw [hbn]; norm_num⟩
    · exact ⟨-1, by rw [hbneg]; norm_num⟩
  have hodd : ∀ m ∈ ({n, -n} : Set Vec3), -m ∈ ({n, -n} : Set Vec3) → b (-m) = -b m := by
    rintro m (rfl | rfl) -
    · rw [hbn, hbneg]
    · rw [neg_neg, hbn, hbneg]; ring
  have hcontb : Continuous fun s : Sph => b (s : Vec3) := by
    rw [hb]
    exact (continuous_const.mul ((continuous_h3_left n).comp continuous_subtype_val))
  have hjr : IsJointlyRegularFamily (famOf (fun _ => 0) b) :=
    jointlyRegular_famOf continuous_const hcontb
  have hex : IsTransformationValuedOn ({n, -n} : Set Vec3) (famOf (fun _ => 0) b) :=
    famOfZ_exact_on hunit hhalf hodd
  have hrates : ∀ m : Vec3, IsUnitAxis m → rateBeta (famOf (fun _ => 0) b) m = b m := by
    intro m hm
    exact ((regular_family_arbitrary_parameters (fun _ => 0) b).2 m hm).2
  exact ⟨⟨hunit, ⟨_, hjr, hex⟩⟩,
    ⟨_, hjr, hex, by rw [hrates n hn, hbn], by rw [hrates (-n) hnnu, hbneg]⟩⟩

/-! ## §39 — absence of antipodal pairs is sufficient -/

/-- **PRINCIPAL THEOREM (§39).**  Every antipodal-free set of unit directions is
admissible, and *every* explicit local model is an exact representative on it. -/
theorem antipodalFree_admissible {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hfree : AntipodalFree D) :
    (∀ k : ℤ, IsTransformationValuedOn D (locFam k)) ∧ IsAdmissibleDomain D := by
  have hmain : ∀ k : ℤ, IsTransformationValuedOn D (locFam k) := by
    intro k
    have hb : IsTransformationValuedOn D (famOf (fun _ => 0) (fun _ => (k : ℝ) + 1 / 2)) :=
      famOfZ_exact_on hunit (fun n _ => ⟨k, rfl⟩) (fun n hn hneg => absurd hneg (hfree n hn))
    rw [locFam_eq_famOf]
    exact hb
  exact ⟨hmain, hunit, ⟨locFam 0, locFam_jointlyRegular 0, hmain 0⟩⟩

/-! ## §40 — the exact criterion -/

/-- **PRINCIPAL THEOREM (§40).**  A set of unit directions is admissible **iff** there is a
rate function, continuous on all unit directions, half-odd on `D`, and odd on every
antipodal pair contained in `D`.  Necessity and sufficiency both hold, so no further
condition is missing. -/
theorem admissible_iff_exists_rate_function {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n) :
    IsAdmissibleDomain D ↔ ∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
      (∀ n ∈ D, ∃ k : ℤ, b n = (k : ℝ) + 1 / 2) ∧ (∀ n ∈ D, -n ∈ D → b (-n) = -b n) := by
  constructor
  · rintro ⟨-, U, hU, hexact⟩
    obtain ⟨-, hhalf, hcont, hodd⟩ := admissible_necessary hU hunit hexact
    exact ⟨rateBeta U, hcont, hhalf, hodd⟩
  · rintro ⟨b, hcont, hhalf, hodd⟩
    exact ⟨hunit, famOf (fun _ => 0) b, jointlyRegular_famOf continuous_const hcont,
      famOfZ_exact_on hunit hhalf hodd⟩

/-! ## §41 — connectedness and the local label -/

/-- **PRINCIPAL THEOREM (§41), positive half.**  On a preconnected admissible domain the
recovered discrete rate is constant, so the local label is unique. -/
theorem label_const_of_preconnected {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n) (hpre : IsPreconnected (sphSet D))
    (hexact : IsTransformationValuedOn D U) :
    ∀ n ∈ D, ∀ m ∈ D, rateBeta U n = rateBeta U m := by
  have hcont : ContinuousOn (fun s : Sph => rateBeta U (s : Vec3)) (sphSet D) :=
    (jointlyRegular_beta_continuous hU).continuousOn
  have hint : ∀ s ∈ sphSet D, ∃ k : ℤ, rateBeta U (s : Vec3) = (k : ℝ) + 1 / 2 := by
    intro s hs
    exact (pointwise_rates hU hexact hs s.2).2
  have hconst := halfodd_const_of_preconnected hpre hcont hint
  intro n hn m hm
  exact hconst ⟨n, hunit n hn⟩ hn ⟨m, hunit m hm⟩ hm

/-- **PRINCIPAL THEOREM (§41), negative half.**  Without a connectedness hypothesis the
label is *not* constant: the two-point admissible domain of §38 carries two different
labels at once. -/
theorem label_not_const_without_connectedness {n : Vec3} (hn : IsUnitAxis n) :
    ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧
      IsTransformationValuedOn ({n, -n} : Set Vec3) U ∧
      rateBeta U n ≠ rateBeta U (-n) := by
  obtain ⟨-, U, hU, hexact, h1, h2⟩ := antipodal_pair_admissible hn
  exact ⟨U, hU, hexact, by rw [h1, h2]; norm_num⟩

/-! ## §42 — an admissible open path-connected domain inside no inherited domain -/

/-- **NEUTRAL DEFINITION.**  The three reference directions of the explicit domain of §42,
together with the auxiliary direction and the three transverse directions.  Only rational
coordinates are used. -/
def eThree : Vec3 := (0, 0, 1)

def pOne : Vec3 := (1, 0, 0)
def pTwo : Vec3 := (0, 1, 0)
noncomputable def pThree : Vec3 := (-3 / 5, -4 / 5, 0)

def mOne : Vec3 := (0, 1, 0)
def mTwo : Vec3 := (-1, 0, 0)
noncomputable def mThree : Vec3 := (4 / 5, -3 / 5, 0)

/-- **NEUTRAL DEFINITION.**  One open leg: a thin wedge around the plane spanned by
`eThree` and `p`, leaning towards `p`.  Both defining inequalities are strict and linear in
the direction, and both defining normals have positive third coordinate. -/
def legCond (p m : Vec3) (n : Vec3) : Prop :=
  h3 n m < (1 / 100) * h3 n p + n.2.2 ∧ -h3 n m < (1 / 100) * h3 n p + n.2.2

/-- **NEUTRAL DEFINITION.**  The explicit domain of §42: the unit directions lying in one
of the three legs. -/
def YDom : Set Vec3 :=
  {n : Vec3 | IsUnitAxis n ∧
    (legCond pOne mOne n ∨ legCond pTwo mTwo n ∨ legCond pThree mThree n)}

theorem legCond_pos {p m n : Vec3} (h : legCond p m n) :
    0 < (1 / 100) * h3 n p + n.2.2 := by
  rcases h with ⟨h1, h2⟩
  linarith

theorem legCond_smul {p m n : Vec3} {c : ℝ} (hc : 0 < c) (h : legCond p m n) :
    legCond p m (c • n) := by
  rcases h with ⟨h1, h2⟩
  constructor <;>
    · simp only [h3_smul_left, Prod.smul_snd, smul_eq_mul]
      nlinarith [h1, h2, hc]

theorem pos_combo {s t k₁ k₂ : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 < s + t) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) : 0 < s * k₁ + t * k₂ := by
  rcases eq_or_lt_of_le hs with h | h
  · have ht' : 0 < t := by linarith
    have := mul_pos ht' hk₂
    nlinarith [mul_nonneg hs hk₁.le]
  · nlinarith [mul_nonneg ht hk₂.le, mul_pos h hk₁]

theorem legCond_add {p m u w : Vec3} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 < s + t)
    (hu : legCond p m u) (hw : legCond p m w) : legCond p m (s • u + t • w) := by
  rcases hu with ⟨hu1, hu2⟩
  rcases hw with ⟨hw1, hw2⟩
  have k1 : 0 < (1 / 100) * h3 u p + u.2.2 - h3 u m := by linarith
  have k2 : 0 < (1 / 100) * h3 w p + w.2.2 - h3 w m := by linarith
  have k1' : 0 < (1 / 100) * h3 u p + u.2.2 + h3 u m := by linarith
  have k2' : 0 < (1 / 100) * h3 w p + w.2.2 + h3 w m := by linarith
  have hc1 := pos_combo hs ht hst k1 k2
  have hc2 := pos_combo hs ht hst k1' k2'
  constructor <;>
    · simp only [h3_add_left, h3_smul_left, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [hc1, hc2]

theorem eThree_isUnitAxis : IsUnitAxis eThree := by
  simp [IsUnitAxis, h3, dot3, eThree]

theorem legCond_eThree (p m : Vec3) (hp : p.2.2 = 0) (hm : m.2.2 = 0) :
    legCond p m eThree := by
  constructor <;> simp [h3, dot3, eThree, hp, hm]

theorem eThree_mem_YDom : eThree ∈ YDom :=
  ⟨eThree_isUnitAxis, Or.inl (legCond_eThree pOne mOne rfl rfl)⟩

/-- **DERIVED (§42).**  The explicit domain contains no antipodal pair, hence it is
admissible by §39. -/
theorem YDom_antipodalFree : AntipodalFree YDom := by
  rintro n ⟨-, hn⟩ ⟨-, hneg⟩
  simp only [legCond, h3, dot3, pOne, pTwo, pThree, mOne, mTwo, mThree, Prod.fst_neg,
    Prod.snd_neg] at hn hneg
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hneg with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> linarith

theorem YDom_unit : ∀ n ∈ YDom, IsUnitAxis n := fun _ h => h.1

/-- **PRINCIPAL THEOREM (§42), admissibility.** -/
theorem YDom_admissible : IsAdmissibleDomain YDom :=
  (antipodalFree_admissible YDom_unit YDom_antipodalFree).2

/-- **PRINCIPAL THEOREM (§42), openness.** -/
theorem YDom_open : IsOpen (sphSet YDom) := by
  have hcont : ∀ p m : Vec3, IsOpen {s : Sph | legCond p m (s : Vec3)} := by
    intro p m
    have h1 : IsOpen {s : Sph | h3 (s : Vec3) m < (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2} := by
      have hf : Continuous fun s : Sph =>
          (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2 - h3 (s : Vec3) m := by
        have c1 : Continuous fun s : Sph => h3 (s : Vec3) p :=
          (continuous_h3_left p).comp continuous_subtype_val
        have c2 : Continuous fun s : Sph => h3 (s : Vec3) m :=
          (continuous_h3_left m).comp continuous_subtype_val
        have c3 : Continuous fun s : Sph => (s : Vec3).2.2 :=
          (continuous_snd.comp continuous_snd).comp continuous_subtype_val
        exact ((continuous_const.mul c1).add c3).sub c2
      have he : {s : Sph | h3 (s : Vec3) m < (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2}
          = (fun s : Sph => (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2
              - h3 (s : Vec3) m) ⁻¹' Set.Ioi 0 := by
        ext s; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]; constructor <;>
          intro h <;> linarith
      rw [he]
      exact hf.isOpen_preimage _ isOpen_Ioi
    have h2 : IsOpen {s : Sph |
        -h3 (s : Vec3) m < (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2} := by
      have hf : Continuous fun s : Sph =>
          (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2 + h3 (s : Vec3) m := by
        have c1 : Continuous fun s : Sph => h3 (s : Vec3) p :=
          (continuous_h3_left p).comp continuous_subtype_val
        have c2 : Continuous fun s : Sph => h3 (s : Vec3) m :=
          (continuous_h3_left m).comp continuous_subtype_val
        have c3 : Continuous fun s : Sph => (s : Vec3).2.2 :=
          (continuous_snd.comp continuous_snd).comp continuous_subtype_val
        exact ((continuous_const.mul c1).add c3).add c2
      have he : {s : Sph | -h3 (s : Vec3) m < (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2}
          = (fun s : Sph => (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2
              + h3 (s : Vec3) m) ⁻¹' Set.Ioi 0 := by
        ext s; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]; constructor <;>
          intro h <;> linarith
      rw [he]
      exact hf.isOpen_preimage _ isOpen_Ioi
    have he : {s : Sph | legCond p m (s : Vec3)}
        = {s : Sph | h3 (s : Vec3) m < (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2} ∩
          {s : Sph | -h3 (s : Vec3) m < (1 / 100) * h3 (s : Vec3) p + (s : Vec3).2.2} := by
      ext s; exact Iff.rfl
    rw [he]
    exact h1.inter h2
  have he : sphSet YDom = {s : Sph | legCond pOne mOne (s : Vec3)} ∪
      ({s : Sph | legCond pTwo mTwo (s : Vec3)} ∪
        {s : Sph | legCond pThree mThree (s : Vec3)}) := by
    ext s
    simp only [mem_sphSet, YDom, Set.mem_setOf_eq, Set.mem_union]
    exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
  rw [he]
  exact (hcont _ _).union ((hcont _ _).union (hcont _ _))

/-- **PRINCIPAL THEOREM (§42), path-connectedness.**  Every member of the explicit domain
is joined to the auxiliary direction inside the domain by the renormalized straight-line
path. -/
theorem YDom_pathConnected : IsPathConnected (sphSet YDom) := by
  refine ⟨⟨eThree, eThree_isUnitAxis⟩, eThree_mem_YDom, ?_⟩
  intro s hs
  have hmemS : (s : Vec3) ∈ YDom := hs
  have hkey : ∀ (p m : Vec3), p.2.2 = 0 → m.2.2 = 0 → legCond p m (s : Vec3) →
      (∀ x : Vec3, legCond p m x →
        (legCond pOne mOne x ∨ legCond pTwo mTwo x ∨ legCond pThree mThree x)) →
      JoinedIn (sphSet YDom) ⟨eThree, eThree_isUnitAxis⟩ s := by
    intro p m hp hm hleg hin
    have hlegE : legCond p m eThree := legCond_eThree p m hp hm
    have hconv : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        legCond p m (segLin eThree (s : Vec3) t) := by
      intro t ht
      exact legCond_add (by linarith [ht.2]) ht.1 (by linarith [ht.1, ht.2]) hlegE hleg
    have hne : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → segLin eThree (s : Vec3) t ≠ 0 := by
      intro t ht hzero
      have := legCond_pos (hconv t ht)
      rw [hzero] at this
      simp [h3, dot3] at this
    refine joinedIn_segPath eThree_isUnitAxis s.2 hne ?_
    intro t ht
    refine ⟨nrmz_isUnitAxis (hne t ht), ?_⟩
    have hsc : legCond p m (segPath eThree (s : Vec3) t) := by
      rw [segPath, nrmz]
      exact legCond_smul (inv_pos.2 (nrm_pos (hne t ht))) (hconv t ht)
    exact hin _ hsc
  rcases hmemS.2 with h | h | h
  · exact hkey pOne mOne rfl rfl h (fun x hx => Or.inl hx)
  · exact hkey pTwo mTwo rfl rfl h (fun x hx => Or.inr (Or.inl hx))
  · exact hkey pThree mThree rfl rfl h (fun x hx => Or.inr (Or.inr hx))

/-- **PRINCIPAL THEOREM (§42): REFUTATION.**  The explicit admissible open path-connected
domain is contained in **no** inherited domain `Dom v`.  Hence "admissible + connected +
open" does not imply "of Task-16 form", and the inherited domains are not exhaustive. -/
theorem YDom_not_subset_Dom (v : Vec3) : ¬ YDom ⊆ Dom v := by
  intro hsub
  -- the four explicit members of the domain
  have hmem : ∀ w : Vec3, IsUnitAxis (nrmz w) → w ≠ 0 →
      (legCond pOne mOne w ∨ legCond pTwo mTwo w ∨ legCond pThree mThree w) →
      0 < h3 w v := by
    intro w hu hw hleg
    have hz : nrmz w ∈ YDom := by
      refine ⟨hu, ?_⟩
      rcases hleg with h | h | h
      · exact Or.inl (by rw [nrmz]; exact legCond_smul (inv_pos.2 (nrm_pos hw)) h)
      · exact Or.inr (Or.inl (by rw [nrmz]; exact legCond_smul (inv_pos.2 (nrm_pos hw)) h))
      · exact Or.inr (Or.inr (by rw [nrmz]; exact legCond_smul (inv_pos.2 (nrm_pos hw)) h))
    exact (nrmz_pos_iff hw v).1 (hsub hz).2
  have hE : 0 < h3 eThree v := (hsub eThree_mem_YDom).2
  have hw1 : (0 : ℝ) < h3 ((1, 0, -1 / 1000) : Vec3) v := by
    refine hmem _ (nrmz_isUnitAxis ?_) ?_ (Or.inl ?_)
    · intro hcon
      have := congrArg (fun w : Vec3 => w.1) hcon
      norm_num at this
    · intro hcon
      have := congrArg (fun w : Vec3 => w.1) hcon
      norm_num at this
    · constructor <;> norm_num [legCond, h3, dot3, pOne, mOne]
  have hw2 : (0 : ℝ) < h3 ((0, 1, -1 / 1000) : Vec3) v := by
    refine hmem _ (nrmz_isUnitAxis ?_) ?_ (Or.inr (Or.inl ?_))
    · intro hcon
      have := congrArg (fun w : Vec3 => w.2.1) hcon
      norm_num at this
    · intro hcon
      have := congrArg (fun w : Vec3 => w.2.1) hcon
      norm_num at this
    · constructor <;> norm_num [legCond, h3, dot3, pTwo, mTwo]
  have hw3 : (0 : ℝ) < h3 ((-3 / 5, -4 / 5, -1 / 1000) : Vec3) v := by
    refine hmem _ (nrmz_isUnitAxis ?_) ?_ (Or.inr (Or.inr ?_))
    · intro hcon
      have := congrArg (fun w : Vec3 => w.1) hcon
      norm_num at this
    · intro hcon
      have := congrArg (fun w : Vec3 => w.1) hcon
      norm_num at this
    · constructor <;> norm_num [legCond, h3, dot3, pThree, mThree]
  -- the positive combination of the three members is a negative multiple of `eThree`
  have hcomb : 3 * h3 ((1, 0, -1 / 1000) : Vec3) v + 4 * h3 ((0, 1, -1 / 1000) : Vec3) v
      + 5 * h3 ((-3 / 5, -4 / 5, -1 / 1000) : Vec3) v = -(12 / 1000) * h3 eThree v := by
    simp only [h3, dot3, eThree]
    ring
  nlinarith [hE, hw1, hw2, hw3, hcomb]

/-! ## §43 — the inherited domains are not maximal -/

/-- **PRINCIPAL THEOREM (§43).**  No inherited domain is maximal among admissible domains:
for every nonzero `v` there is an admissible domain strictly containing `Dom v`.  (Nothing
in Task 16 or Task 17 asserts minimality or maximality of `Dom v`.) -/
theorem Dom_not_maximal {v : Vec3} (hv : v ≠ 0) :
    ∃ D : Set Vec3, Dom v ⊂ D ∧ IsAdmissibleDomain D := by
  obtain ⟨m, hm, hmv⟩ := exists_unit_orthogonal (nrmz_isUnitAxis hv)
  have hmv' : h3 m v = 0 := by
    have h := hmv
    rw [h3_nrmz_left] at h
    have hnz : (nrm v)⁻¹ ≠ 0 := by
      simp only [ne_eq, inv_eq_zero]
      exact ne_of_gt (nrm_pos hv)
    have : h3 v m = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hnz
      · exact h'
    rw [h3_comm]
    exact this
  refine ⟨insert m (Dom v), ⟨Set.subset_insert _ _, ?_⟩, ?_⟩
  · intro hsub
    have := hsub (Set.mem_insert m (Dom v))
    rw [mem_Dom_iff] at this
    rw [hmv'] at this
    exact absurd this.2 (lt_irrefl 0)
  · refine (antipodalFree_admissible ?_ ?_).2
    · rintro n (rfl | hn)
      · exact hm
      · exact hn.1
    · rintro n (rfl | hn) hneg
      · rcases hneg with hneg | hneg
        · have hcontra := congrArg (fun w : Vec3 => h3 w n) hneg
          simp only [h3_neg_left] at hcontra
          have hnn : h3 n n = 1 := hm
          rw [hnn] at hcontra
          norm_num at hcontra
        · have := hneg.2
          rw [h3_neg_left, hmv'] at this
          exact absurd this (by norm_num)
      · rcases hneg with hneg | hneg
        · have hnn : h3 n v = 0 := by
            have : -n = m := hneg
            have := congrArg (fun w : Vec3 => h3 w v) this
            simp only [h3_neg_left] at this
            rw [hmv'] at this
            linarith
          exact absurd hn.2 (by rw [hnn]; exact lt_irrefl 0)
        · exact Dom_antipodal_free hn hneg

end NullSectorTask17
