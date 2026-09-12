import RequestProject.Experiment2.NullSectorTask17.AdmissibleDomains

/-!
# Task 17, Package E: arbitrary overlap transitions

Task 16 computed the transition factor between two *explicit* local models.  Here the
factor is **derived** for arbitrary locally classified exact jointly regular families on
arbitrary admissible domains (§45, §46), and its properties are established:

* §47.  The relative factor is central (and a central unit).
* §48.  On a preconnected subset of the overlap on which both families are exact, the
  factor does not depend on the direction.
* §49.  Its dependence on the transformation parameter is exactly the inherited
  one-parameter central law `θ ↦ zexp 0 j θ` with an **integer** `j`, the difference of the
  two local labels; in particular it is multiplicative in the parameter.
* §50.  Uniqueness: the factor is the only element of the carrier implementing the
  comparison, under the inherited normalization of the two families at the identity
  parameter.
* §51.  For three families the pairwise factors compose.
* §52.  The composition law extends to an arbitrary **finite** chain of families, by
  induction on the length of the chain.
* §53.  Only finite chains occur: no infinite product of transition factors is defined
  anywhere in Task 17, and none is used.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## §45, §46 — the derived relative factor -/

/-- **NEUTRAL DEFINITION (§46).**  The relative internal factor of two families at a
direction and a parameter.  It is *derived* from the two families, not read off from any
explicit model. -/
noncomputable def ovl (U V : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) : W := U n θ ⋆ V n (-θ)

/-- **PRINCIPAL THEOREM (§46, §47).**  For two jointly regular families the relative factor
is central and implements the comparison of the two families at every direction and
parameter. -/
theorem ovl_central_and_factor {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    ovl U V n θ ∈ Z ∧ U n θ = ovl U V n θ ⋆ V n θ :=
  overlap_defect_central hU.toRegularFamily hV.toRegularFamily hn θ

/-- **PRINCIPAL THEOREM (§50).**  The relative factor is unique: any element of the carrier
implementing the comparison at a direction and parameter equals it. -/
theorem ovl_unique {U V : Vec3 → ℝ → W} (hV : IsJointlyRegularFamily V) {n : Vec3}
    (hn : IsUnitAxis n) {θ : ℝ} {c : W} (h : U n θ = c ⋆ V n θ) : c = ovl U V n θ := by
  have hinv : V n θ ⋆ V n (-θ) = w1 := (hV.lift n hn).mul_neg θ
  calc c = c ⋆ w1 := by rw [mul_one_W]
    _ = c ⋆ (V n θ ⋆ V n (-θ)) := by rw [hinv]
    _ = (c ⋆ V n θ) ⋆ V n (-θ) := by rw [mul_assoc_W]
    _ = U n θ ⋆ V n (-θ) := by rw [← h]
    _ = ovl U V n θ := rfl

/-! ## §49 — the exact parameter dependence -/

theorem central_swap_mul {a x b y : W} (hb : b ∈ Z) :
    (a ⋆ x) ⋆ (b ⋆ y) = (a ⋆ b) ⋆ (x ⋆ y) := by
  calc (a ⋆ x) ⋆ (b ⋆ y) = a ⋆ ((x ⋆ b) ⋆ y) := by simp only [mul_assoc_W]
    _ = a ⋆ ((b ⋆ x) ⋆ y) := by rw [Z_central hb]
    _ = (a ⋆ b) ⋆ (x ⋆ y) := by simp only [mul_assoc_W]

/-- **DERIVED.**  Reversal of the parameter is reversal of the rate. -/
theorem zexp_zero_neg' (c θ : ℝ) : zexp 0 c (-θ) = zexp 0 (-c) θ := (zexp_zero_neg c θ).symm

theorem zexp_mem_Z (a b θ : ℝ) : zexp a b θ ∈ Z := by
  rw [zexp]; exact zc_mem_Z _ _

/-- **PRINCIPAL THEOREM (§49), explicit form.**  If the two families have vanishing first
recovered rate at the direction, the relative factor is exactly the inherited central
one-parameter element attached to the difference of the two second rates. -/
theorem ovl_explicit {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {n : Vec3} (hn : IsUnitAxis n)
    (hαU : rateAlpha U n = 0) (hαV : rateAlpha V n = 0) (θ : ℝ) :
    ovl U V n θ = zexp 0 (rateBeta U n - rateBeta V n) θ := by
  have h1 := recovered_form hU hn θ
  have h2 := recovered_form hV hn (-θ)
  calc ovl U V n θ = (zexp 0 (rateBeta U n) θ ⋆ Un n θ)
        ⋆ (zexp 0 (rateBeta V n) (-θ) ⋆ Un n (-θ)) := by
        rw [ovl, h1, h2, hαU, hαV]
    _ = (zexp 0 (rateBeta U n) θ ⋆ zexp 0 (rateBeta V n) (-θ)) ⋆ (Un n θ ⋆ Un n (-θ)) :=
        central_swap_mul (zexp_mem_Z _ _ _)
    _ = zexp 0 (rateBeta U n) θ ⋆ zexp 0 (-rateBeta V n) θ := by
        rw [Un_mul_neg hn, mul_one_W, zexp_zero_neg']
    _ = zexp 0 (rateBeta U n - rateBeta V n) θ := by
        rw [zexp_zero_add, sub_eq_add_neg]

/-- **PRINCIPAL THEOREM (§49), the parameter law.**  The relative factor is multiplicative
in the transformation parameter and trivial at the identity parameter. -/
theorem ovl_param_law {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {n : Vec3} (hn : IsUnitAxis n)
    (hαU : rateAlpha U n = 0) (hαV : rateAlpha V n = 0) (θ φ : ℝ) :
    ovl U V n (θ + φ) = ovl U V n θ ⋆ ovl U V n φ ∧ ovl U V n 0 = w1 := by
  constructor
  · rw [ovl_explicit hU hV hn hαU hαV, ovl_explicit hU hV hn hαU hαV,
      ovl_explicit hU hV hn hαU hαV]
    exact (zexp_isCentralHom 0 (rateBeta U n - rateBeta V n)).mul θ φ
  · rw [ovl_explicit hU hV hn hαU hαV]
    exact (zexp_isCentralHom 0 (rateBeta U n - rateBeta V n)).unit

/-! ## The integer overlap label -/

/-- **PRINCIPAL THEOREM (§46, §49).**  If both families are exact on sets containing the
direction, the relative factor is the central one-parameter element attached to an
**integer**: the difference of the two local labels. -/
theorem ovl_integer {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {DU DV : Set Vec3}
    (hexU : IsTransformationValuedOn DU U) (hexV : IsTransformationValuedOn DV V)
    {n : Vec3} (hnU : n ∈ DU) (hnV : n ∈ DV) (hn : IsUnitAxis n) :
    ∃ j : ℤ, ∀ θ : ℝ, ovl U V n θ = zexp 0 (j : ℝ) θ := by
  obtain ⟨hαU, kU, hkU⟩ : rateAlpha U n = 0 ∧ ∃ k : ℤ, rateBeta U n = (k : ℝ) + 1 / 2 :=
    pointwise_rates hU hexU hnU hn
  obtain ⟨hαV, kV, hkV⟩ : rateAlpha V n = 0 ∧ ∃ k : ℤ, rateBeta V n = (k : ℝ) + 1 / 2 :=
    pointwise_rates hV hexV hnV hn
  refine ⟨kU - kV, fun θ => ?_⟩
  rw [ovl_explicit hU hV hn hαU hαV, hkU, hkV]
  congr 1
  push_cast
  ring

/-! ## §48 — independence of the direction on a preconnected overlap -/

/-- **PRINCIPAL THEOREM (§48).**  On a preconnected set of unit directions on which both
families are exact, the relative factor does not depend on the direction. -/
theorem ovl_direction_independent {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hpre : IsPreconnected (sphSet D)) (hexU : IsTransformationValuedOn D U)
    (hexV : IsTransformationValuedOn D V) :
    ∀ n ∈ D, ∀ m ∈ D, ∀ θ : ℝ, ovl U V n θ = ovl U V m θ := by
  intro n hn m hm θ
  have hbU := label_const_of_preconnected hU hunit hpre hexU n hn m hm
  have hbV := label_const_of_preconnected hV hunit hpre hexV n hn m hm
  have hαUn := (pointwise_rates hU hexU hn (hunit n hn)).1
  have hαUm := (pointwise_rates hU hexU hm (hunit m hm)).1
  have hαVn := (pointwise_rates hV hexV hn (hunit n hn)).1
  have hαVm := (pointwise_rates hV hexV hm (hunit m hm)).1
  rw [ovl_explicit hU hV (hunit n hn) hαUn hαVn, ovl_explicit hU hV (hunit m hm) hαUm hαVm,
    hbU, hbV]

/-! ## §51, §52 — composition of transitions -/

/-- **PRINCIPAL THEOREM (§51).**  For three families the pairwise relative factors compose:
the composite of the two transitions is the direct transition.  Only associativity and the
inherited one-axis inverse law are used. -/
theorem ovl_chain3 {U V T : Vec3 → ℝ → W} (hV : IsJointlyRegularFamily V) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) : ovl U V n θ ⋆ ovl V T n θ = ovl U T n θ := by
  have hinv : V n (-θ) ⋆ V n θ = w1 := (hV.lift n hn).neg_mul θ
  calc ovl U V n θ ⋆ ovl V T n θ
      = U n θ ⋆ ((V n (-θ) ⋆ V n θ) ⋆ T n (-θ)) := by
        simp only [ovl, mul_assoc_W]
    _ = U n θ ⋆ T n (-θ) := by rw [hinv, one_mul_W]
    _ = ovl U T n θ := rfl

/-- **NEUTRAL DEFINITION (§52).**  The composite of the transition factors along a finite
chain of families, indexed by the natural numbers up to a finite length.  No infinite
product occurs: the composite of a chain of length `N` is a finite iterated product. -/
noncomputable def chainOvl (F : ℕ → Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) : ℕ → W
  | 0 => w1
  | (j + 1) => chainOvl F n θ j ⋆ ovl (F j) (F (j + 1)) n θ

/-- **PRINCIPAL THEOREM (§52).**  For an arbitrary **finite** chain of jointly regular
families the composite of the successive transition factors is the direct transition
between the two ends of the chain.  The statement is about a chain of arbitrary finite
length; no infinite product is defined or used (§53). -/
theorem chainOvl_eq (F : ℕ → Vec3 → ℝ → W) (hF : ∀ j : ℕ, IsJointlyRegularFamily (F j))
    {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    ∀ N : ℕ, chainOvl F n θ N = ovl (F 0) (F N) n θ := by
  intro N
  induction N with
  | zero =>
      have hinv : F 0 n θ ⋆ F 0 n (-θ) = w1 := ((hF 0).lift n hn).mul_neg θ
      rw [chainOvl, ovl, hinv]
  | succ j ih =>
      rw [chainOvl, ih, ovl_chain3 (hF j) hn]

end NullSectorTask17
