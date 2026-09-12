import RequestProject.Experiment2.NullSectorTask19.DisconnectedExtension

/-!
# Task 19, Package G: complete visible-relation coverage

The Task-16 coincidence classification is used as **fixed input** (§58); nothing about it is
re-derived here.

* §59.  `VisRelation` is the intrinsic relation object attached to two axis–parameter pairs
  which generate the same visible transformation.
* §60.  `visRelation_trichotomy` separates the three proved classes: same-direction,
  antipodal, and the identity-degenerate parameter class.
* §61.  `RelationSatisfiedBy` is the minimal explicit comparison datum: one equation between
  the two internal representatives.  It is required exactly when the two members of the
  relation are not both inside one local domain.
* §62.  The same-direction class is **automatic** for every jointly regular family whose
  first rate vanishes and whose directional rate is half-odd — the local one-parameter law
  already forces `2π`-periodicity.
* §63.  The identity-degenerate class is **automatic** for the same families: every one of
  them takes the value `w1` at every integer multiple of `2π`.
* §64.  The antipodal class is the **only** remaining nonautomatic class: adding it to a
  family with vanishing first rate and half-odd directional rate yields full relation
  completeness, and conversely relation completeness returns it.  It is genuinely
  nonautomatic: an explicit family satisfying the other two classes fails it.
* §66.  `IsRelationComplete` and `SystemRelationComplete` are defined by quantification over
  the relation itself, never over set-theoretic coverage of directions.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## §59 — the intrinsic relation object -/

/-- **NEUTRAL DEFINITION (§59).**  The intrinsic relation object: two axis–parameter pairs
generate the same visible transformation.  This is the Task-16 coincidence, used as fixed
input. -/
def VisRelation (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) : Prop := Coincident n θ m φ

theorem visRelation_iff (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) :
    VisRelation n θ m φ ↔ PhiGen n θ = PhiGen m φ := Iff.rfl

/-! ## §60 — the three proved classes -/

/-- **NEUTRAL DEFINITION (§60).**  The same-direction class. -/
def SameDirectionRel (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) : Prop :=
  m = n ∧ VisRelation n θ m φ

/-- **NEUTRAL DEFINITION (§60).**  The antipodal class. -/
def AntipodalRel (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) : Prop :=
  m = -n ∧ VisRelation n θ m φ

/-- **NEUTRAL DEFINITION (§60).**  The identity-degenerate parameter class: both parameters
lie in `2πℤ`, so the visible transformation is the identity and the direction is not
determined at all. -/
def DegenerateRel (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) : Prop :=
  (∃ k : ℤ, θ = 2 * Real.pi * k) ∧ (∃ l : ℤ, φ = 2 * Real.pi * l) ∧ VisRelation n θ m φ

/-- **PRINCIPAL THEOREM (§60).**  Every visible relation lies in one of the three classes.
This is the Task-16 classification, used as fixed input. -/
theorem visRelation_trichotomy {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    {θ φ : ℝ} (h : VisRelation n θ m φ) :
    SameDirectionRel n θ m φ ∨ AntipodalRel n θ m φ ∨ DegenerateRel n θ m φ := by
  rcases coincidence_cross_classification hn hm h with h1 | h1 | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr (Or.inl ⟨h1, h⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, h⟩)

/-! ## §61 — the minimal comparison datum -/

/-- **NEUTRAL DEFINITION (§61).**  The minimal explicit comparison datum attached to one
visible relation: the single equation identifying the two internal representatives.  When
both members of the relation lie inside one admissible domain this equation is already part
of exactness on that domain; when they do not, it is genuinely extra data. -/
def RelationSatisfiedBy (U : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) : Prop :=
  U n θ = U m φ

/-- **DERIVED (§61).**  If both members of a relation lie in one admissible domain, the
comparison datum is already implied by exactness on that domain — no extra datum is
required. -/
theorem relationSatisfied_of_mem_common_domain {D : Set Vec3} {U : Vec3 → ℝ → W}
    (hexact : IsTransformationValuedOn D U) {n m : Vec3} (hn : n ∈ D) (hm : m ∈ D) {θ φ : ℝ}
    (h : VisRelation n θ m φ) : RelationSatisfiedBy U n θ m φ :=
  hexact n hn m hm θ φ h

/-! ## §66 — relation completeness, independent of direction coverage -/

/-- **NEUTRAL DEFINITION (§66).**  A single family is *relation complete* when every visible
relation between unit directions is satisfied by it.  The quantification is over relations,
not over any covering of the direction space by domains. -/
def IsRelationComplete (U : Vec3 → ℝ → W) : Prop :=
  ∀ n m : Vec3, IsUnitAxis n → IsUnitAxis m → ∀ θ φ : ℝ,
    VisRelation n θ m φ → RelationSatisfiedBy U n θ m φ

/-- **NEUTRAL DEFINITION (§66).**  An indexed local system is *relation complete* when every
visible relation is satisfied *across* the system: whichever local members see the two
directions, their representatives agree.  Again no set-theoretic coverage is asserted. -/
def SystemRelationComplete {ι : Type*} (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W) : Prop :=
  ∀ (i j : ι) (n m : Vec3), n ∈ D i → m ∈ D j → ∀ θ φ : ℝ,
    VisRelation n θ m φ → U i n θ = U j m φ

theorem relationComplete_iff_transformationValued {U : Vec3 → ℝ → W} :
    IsRelationComplete U ↔ IsTransformationValued U :=
  ⟨fun h n m θ φ hn hm hP => h n m hn hm θ φ hP, fun h n m hn hm θ φ hP => h n m θ φ hn hm hP⟩

/-! ## The rate hypothesis under which the two easy classes become automatic -/

/-- **NEUTRAL DEFINITION.**  The pointwise rate hypothesis satisfied by every locally exact
jointly regular family: vanishing first rate and half-odd directional rate. -/
def RateZeroHalfOdd (U : Vec3 → ℝ → W) : Prop :=
  ∀ n : Vec3, IsUnitAxis n → rateAlpha U n = 0 ∧ IsHalfOdd (rateBeta U n)

/-- **DERIVED.**  A locally exact jointly regular family satisfies the rate hypothesis. -/
theorem rateZeroHalfOdd_of_locallyExact {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hloc : IsLocallyExact U) : RateZeroHalfOdd U := by
  intro n hn
  obtain ⟨hα, k, hk⟩ :=
    pointwise_rates hU (hloc n (isUnitAxis_ne_zero hn)) (Dom_covers hn) hn
  exact ⟨hα, k, hk⟩

/-! ## §62 — the same-direction class is automatic -/

theorem zc_neg (a b : ℝ) : zc (-a) (-b) = -zc a b := by rw [zc, zc]; module

/-- **DERIVED.**  A half-odd central rate changes the sign of the central factor over one
full parameter turn. -/
theorem zexp_zero_halfOdd_add_two_pi {b : ℝ} (hb : IsHalfOdd b) (θ : ℝ) :
    zexp 0 b (θ + 2 * Real.pi) = -zexp 0 b θ := by
  obtain ⟨k, hk⟩ := hb
  have hcos : Real.cos (b * (θ + 2 * Real.pi)) = -Real.cos (b * θ) := by
    rw [show b * (θ + 2 * Real.pi) = (b * θ + Real.pi) + (k : ℝ) * (2 * Real.pi) by
      rw [hk]; ring, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  have hsin : Real.sin (b * (θ + 2 * Real.pi)) = -Real.sin (b * θ) := by
    rw [show b * (θ + 2 * Real.pi) = (b * θ + Real.pi) + (k : ℝ) * (2 * Real.pi) by
      rw [hk]; ring, Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  rw [zexp_zero_val, zexp_zero_val, hcos, hsin, zc_neg]

/-- **PRINCIPAL THEOREM (§62).**  *The local one-parameter law already forces the full
parameter period.*  A jointly regular family with vanishing first rate and half-odd
directional rate at a direction is `2π`-periodic there. -/
theorem family_periodic {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (hα : rateAlpha U n = 0) (hβ : IsHalfOdd (rateBeta U n)) :
    Function.Periodic (U n) (2 * Real.pi) := by
  intro θ
  rw [recovered_form hU hn (θ + 2 * Real.pi), recovered_form hU hn θ, hα, Un_add_two_pi,
    zexp_zero_halfOdd_add_two_pi hβ, neg_mul_W, mul_neg_W, neg_neg]

/-- **PRINCIPAL THEOREM (§62).**  *Same-direction relations are automatic.*  For a jointly
regular family with vanishing first rate and half-odd directional rate at `n`, every
same-direction relation at `n` is satisfied; no comparison datum is needed. -/
theorem same_direction_automatic {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (hα : rateAlpha U n = 0) (hβ : IsHalfOdd (rateBeta U n)) {θ φ : ℝ}
    (h : VisRelation n θ n φ) : RelationSatisfiedBy U n θ n φ := by
  obtain ⟨k, hk⟩ := (coincidence_same_axis_iff hn θ φ).1 h
  have hθ : θ = φ + (k : ℝ) * (2 * Real.pi) := by linarith [hk]
  show U n θ = U n φ
  rw [hθ]
  exact (family_periodic hU hn hα hβ).int_mul k φ

/-! ## §63 — the identity-degenerate class is automatic -/

/-- **PRINCIPAL THEOREM (§63).**  *The degenerate class is automatic.*  Every jointly
regular family with vanishing first rate and half-odd directional rate takes the value `w1`
at every integer multiple of `2π`, in every direction. -/
theorem family_at_int_two_pi {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (hα : rateAlpha U n = 0) (hβ : IsHalfOdd (rateBeta U n)) (k : ℤ) :
    U n (2 * Real.pi * k) = w1 := by
  have hper := (family_periodic hU hn hα hβ).int_mul k 0
  rw [show 2 * Real.pi * (k : ℝ) = 0 + (k : ℝ) * (2 * Real.pi) by ring, hper]
  exact (hU.lift n hn).unit

/-- **PRINCIPAL THEOREM (§63).**  *Degenerate relations are automatic across arbitrary
directions.*  No comparison datum is needed for the identity-degenerate class. -/
theorem degenerate_automatic {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hrates : RateZeroHalfOdd U) {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    {θ φ : ℝ} (h : DegenerateRel n θ m φ) : RelationSatisfiedBy U n θ m φ := by
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩, -⟩ := h
  show U n θ = U m φ
  rw [hk, hl, family_at_int_two_pi hU hn (hrates n hn).1 (hrates n hn).2 k,
    family_at_int_two_pi hU hm (hrates m hm).1 (hrates m hm).2 l]

/-! ## §64 — the antipodal class is the only nonautomatic one -/

/-- **NEUTRAL DEFINITION (§64).**  The antipodal comparison datum for a single family: the
representative at a reversed direction with reversed parameter agrees with the original. -/
def AntipodalRelated (U : Vec3 → ℝ → W) : Prop :=
  ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = U (-n) (-θ)

/-- **DERIVED.**  The antipodal pair is genuinely a visible relation. -/
theorem antipodal_visRelation (n : Vec3) (θ : ℝ) : VisRelation n θ (-n) (-θ) := by
  show PhiGen n θ = PhiGen (-n) (-θ)
  rw [coincidence_neg_axis n (-θ), neg_neg]

/-- **PRINCIPAL THEOREM (§64), sufficiency.**  Once the antipodal comparison datum is
supplied, a jointly regular family with vanishing first rate and half-odd directional rate
is **relation complete**: the antipodal class is the only nonautomatic class. -/
theorem relationComplete_of_antipodalRelated {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hrates : RateZeroHalfOdd U) (hanti : AntipodalRelated U) : IsRelationComplete U := by
  intro n m hn hm θ φ h
  rcases visRelation_trichotomy hn hm h with ⟨hmn, h'⟩ | ⟨hmn, h'⟩ | hdeg
  · have h'' : PhiGen n θ = PhiGen m φ := h'
    rw [hmn] at h''
    have hP : VisRelation n θ n φ := h''
    show U n θ = U m φ
    rw [hmn]
    exact same_direction_automatic hU hn (hrates n hn).1 (hrates n hn).2 hP
  · have hP : VisRelation n θ n (-φ) := by
      show PhiGen n θ = PhiGen n (-φ)
      refine h'.trans ?_
      rw [hmn]
      exact coincidence_neg_axis n φ
    have h1 : U n θ = U n (-φ) :=
      same_direction_automatic hU hn (hrates n hn).1 (hrates n hn).2 hP
    have h2 : U n (-φ) = U (-n) φ := by
      have := hanti n hn (-φ)
      rwa [neg_neg] at this
    show U n θ = U m φ
    rw [hmn, h1, h2]
  · exact degenerate_automatic hU hrates hn hm hdeg

/-- **PRINCIPAL THEOREM (§64), necessity.**  Relation completeness returns the antipodal
comparison datum. -/
theorem antipodalRelated_of_relationComplete {U : Vec3 → ℝ → W} (h : IsRelationComplete U) :
    AntipodalRelated U :=
  fun n hn θ => h n (-n) hn (isUnitAxis_neg hn) θ (-θ) (antipodal_visRelation n θ)

/-- **PRINCIPAL THEOREM (§64).**  *Exact equivalence.*  For a jointly regular family with
vanishing first rate and half-odd directional rate, relation completeness is **exactly** the
antipodal comparison datum.  The same-direction and identity-degenerate classes contribute
nothing. -/
theorem relationComplete_iff_antipodalRelated {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hrates : RateZeroHalfOdd U) : IsRelationComplete U ↔ AntipodalRelated U :=
  ⟨antipodalRelated_of_relationComplete, relationComplete_of_antipodalRelated hU hrates⟩

/-- **DERIVED.**  The explicit local model with label `0` has vanishing first rate and
half-odd directional rate at every unit direction. -/
theorem locFam_zero_rates : RateZeroHalfOdd (locFam 0) :=
  fun _ hn => ⟨(locFam_rates 0 hn).1, ⟨0, (locFam_rates 0 hn).2⟩⟩

/-- **DERIVED (§64).**  The explicit local model with label `0` fails the antipodal
comparison datum. -/
theorem locFam_zero_not_antipodalRelated : ¬ AntipodalRelated (locFam 0) := by
  intro hanti
  have h := relationComplete_of_antipodalRelated (locFam_jointlyRegular 0) locFam_zero_rates hanti
  exact no_global_jointly_regular_transformationValued
    ⟨locFam 0, locFam_jointlyRegular 0, relationComplete_iff_transformationValued.1 h⟩

/-- **PRINCIPAL THEOREM (§64), the nonautomaticity.**  The antipodal class is genuinely not
automatic: there is a jointly regular family with vanishing first rate and half-odd
directional rate — hence one for which the same-direction and identity-degenerate classes
are automatically satisfied — which fails the antipodal comparison datum. -/
theorem antipodal_class_not_automatic :
    ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ RateZeroHalfOdd U ∧ ¬ AntipodalRelated U :=
  ⟨locFam 0, locFam_jointlyRegular 0, locFam_zero_rates, locFam_zero_not_antipodalRelated⟩

/-- **PRINCIPAL THEOREM (§64), summary.**  Of the three classes, two are automatic for every
locally exact jointly regular family and the third is not. -/
theorem three_classes_status :
    (∀ U : Vec3 → ℝ → W, IsJointlyRegularFamily U → RateZeroHalfOdd U →
      ∀ n : Vec3, IsUnitAxis n → ∀ θ φ : ℝ, SameDirectionRel n θ n φ →
        RelationSatisfiedBy U n θ n φ) ∧
    (∀ U : Vec3 → ℝ → W, IsJointlyRegularFamily U → RateZeroHalfOdd U →
      ∀ n m : Vec3, IsUnitAxis n → IsUnitAxis m → ∀ θ φ : ℝ, DegenerateRel n θ m φ →
        RelationSatisfiedBy U n θ m φ) ∧
    (∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ RateZeroHalfOdd U ∧
      ¬ ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ,
          RelationSatisfiedBy U n θ (-n) (-θ)) := by
  refine ⟨fun U hU hr n hn θ φ h =>
      same_direction_automatic hU hn (hr n hn).1 (hr n hn).2 h.2,
    fun U hU hr n m hn hm θ φ h => degenerate_automatic hU hr hn hm h, ?_⟩
  obtain ⟨U, hU, hr, hno⟩ := antipodal_class_not_automatic
  exact ⟨U, hU, hr, hno⟩

/-! ## §66 — direction coverage does not give relation completeness -/

/-- **NEUTRAL DEFINITION.**  The inherited local system: the inherited domains carry the
explicit local model with label `0`. -/
noncomputable def inhSystem : Vec3 → Vec3 → ℝ → W := fun _ => locFam 0

/-- **PRINCIPAL THEOREM (§66): REFUTATION.**  The inherited local system covers every
direction, has coherent ordinary overlaps (all its members are literally equal), is exact on
every one of its domains, and is nevertheless **not** relation complete.  Relation
completeness is therefore strictly stronger than set-theoretic direction coverage. -/
theorem coverage_not_relationComplete :
    CoversDirections Dom ∧
      (∀ i j : Vec3, ∀ n : Vec3, n ∈ Dom i → n ∈ Dom j →
        ∀ θ : ℝ, inhSystem i n θ = inhSystem j n θ) ∧
      (∀ v : Vec3, v ≠ 0 → IsTransformationValuedOn (Dom v) (inhSystem v)) ∧
      ¬ SystemRelationComplete Dom inhSystem := by
  refine ⟨Dom_coversDirections, fun _ _ _ _ _ _ => rfl,
    fun v _ => locFam_transformationValuedOn 0 v, fun hsys => ?_⟩
  refine locFam_zero_not_antipodalRelated (fun n hn θ => ?_)
  exact hsys n (-n) n (-n) (Dom_covers hn) (Dom_covers (isUnitAxis_neg hn)) θ (-θ)
    (antipodal_visRelation n θ)

end NullSectorTask19
