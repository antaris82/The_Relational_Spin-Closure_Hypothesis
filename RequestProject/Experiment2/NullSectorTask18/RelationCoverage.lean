import RequestProject.Experiment2.NullSectorTask18.GlobalBridgeObstruction

/-!
# Task 18, Package G: ordinary overlaps versus visible coincidence relations

Ordinary domain overlap — `n ∈ D i ∩ D j` — is a statement about **one** direction.  The
visible coincidence relation is more general: two possibly different pairs `(n, θ)` and
`(m, φ)` may generate the same inherited visible transformation (§45).  This module
separates the two notions and settles the coverage question with the *exact* Task-16
coincidence classification, not by assumption.

* §46.  `CoversRelations` — an indexed family of direction domains covers a coincidence
  relation when *both* members of every coincident pair lie in one and the same domain.
  `CoversDirections` is the weaker, ordinary notion.
* §47.  The inherited family `{Dom v}` covers all individual directions but **not** all
  coincidence relations.
* §48.  More strongly: **no** family of antipodal-free domains covers the relations, no
  matter how the domains are chosen; the antipodal relation is never visible inside a
  single antipodal-free domain, although both of its directions are individually
  admissible.
* §49.  The antipodal relation is **not** the only cross-domain relation.  The exact
  classification, derived from `coincidence_iff_coords`, is: two coincident pairs have
  either `m = n`, or `m = -n`, or both parameters in `2πℤ` — the degenerate class in which
  the visible transformation is the identity and the direction is not determined at all.
  This second cross-domain class is exhibited explicitly, and it is proved *harmless*: the
  explicit local models already satisfy it across arbitrary directions.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## §45, §46 — the two coverage notions -/

/-- **NEUTRAL DEFINITION (§45).**  Two axis–parameter pairs generate the same inherited
visible transformation. -/
def Coincident (n : Vec3) (θ : ℝ) (m : Vec3) (φ : ℝ) : Prop := PhiGen n θ = PhiGen m φ

/-- **NEUTRAL DEFINITION (§45).**  Ordinary coverage: every unit direction lies in some
domain. -/
def CoversDirections {ι : Type*} (D : ι → Set Vec3) : Prop :=
  ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i

/-- **NEUTRAL DEFINITION (§46).**  Relation coverage: for every coincident pair of
axis–parameter pairs, *both* directions lie in one and the same domain.  No conventional
groupoid vocabulary is used; the relation is the inherited visible coincidence. -/
def CoversRelations {ι : Type*} (D : ι → Set Vec3) : Prop :=
  ∀ n m : Vec3, IsUnitAxis n → IsUnitAxis m → ∀ θ φ : ℝ, Coincident n θ m φ →
    ∃ i : ι, n ∈ D i ∧ m ∈ D i

/-! ## §47 — the inherited family covers directions but not relations -/

theorem Dom_coversDirections : CoversDirections Dom := fun n hn => ⟨n, Dom_covers hn⟩

/-- **DERIVED.**  The antipodal coincidence, in the non-degenerate parameter range. -/
theorem antipodal_coincident (n : Vec3) :
    Coincident (-n) Real.pi n (-Real.pi) := coincidence_neg_axis n Real.pi

/-- **PRINCIPAL THEOREM (§48).**  **No** family of antipodal-free domains covers the
visible coincidence relations, however the domains are chosen — even though every unit
direction lies in an admissible domain.  The witness is the antipodal relation. -/
theorem antipodalFree_family_not_coversRelations {ι : Type*} {D : ι → Set Vec3}
    (hfree : ∀ i : ι, AntipodalFree (D i)) : ¬ CoversRelations D := by
  intro hcov
  obtain ⟨i, h1, h2⟩ := hcov (-e1) e1 (isUnitAxis_neg e1_isUnitAxis) e1_isUnitAxis
    Real.pi (-Real.pi) (antipodal_coincident e1)
  exact hfree i e1 h2 h1

/-- **PRINCIPAL THEOREM (§47): REFUTATION.**  The inherited family covers every individual
direction, but it does not cover the coincidence relations. -/
theorem Dom_coversDirections_not_coversRelations :
    CoversDirections Dom ∧ ¬ CoversRelations Dom :=
  ⟨Dom_coversDirections,
    antipodalFree_family_not_coversRelations (fun _ _ hn => Dom_antipodal_free hn)⟩

/-! ## §49 — the exact classification of cross-domain relations -/

/-- **DERIVED.**  A vanishing half-parameter sine means the parameter is an integer
multiple of `2π`. -/
theorem sin_half_eq_zero_iff (θ : ℝ) : Real.sin (θ / 2) = 0 ↔ ∃ k : ℤ, θ = 2 * Real.pi * k := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- **PRINCIPAL THEOREM (§49).**  The exact classification of coincident pairs, derived
from the Task-16 coincidence relation: either the two directions agree, or they are
opposite, or the coincidence is degenerate — both parameters lie in `2πℤ`, the visible
transformation is the identity, and the direction is not determined at all. -/
theorem coincidence_cross_classification {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    {θ φ : ℝ} (h : Coincident n θ m φ) :
    m = n ∨ m = -n ∨ ((∃ k : ℤ, θ = 2 * Real.pi * k) ∧ ∃ l : ℤ, φ = 2 * Real.pi * l) := by
  obtain ⟨u, hu, hsv⟩ : ∃ u : ℝ, (u = Real.sin (φ / 2) ∨ u = -Real.sin (φ / 2)) ∧
      Real.sin (θ / 2) • n = u • m := by
    rcases (coincidence_iff_coords hn hm θ φ).1 h with ⟨-, hs⟩ | ⟨-, hs⟩
    · exact ⟨Real.sin (φ / 2), Or.inl rfl, hs⟩
    · refine ⟨-Real.sin (φ / 2), Or.inr rfl, ?_⟩
      rw [hs]; module
  by_cases hs0 : Real.sin (θ / 2) = 0
  · refine Or.inr (Or.inr ⟨(sin_half_eq_zero_iff θ).1 hs0, ?_⟩)
    have hu0 : u = 0 := by
      have : u • m = 0 := by rw [← hsv, hs0, zero_smul]
      exact smul_unit_eq_zero hm this
    have hsφ : Real.sin (φ / 2) = 0 := by
      rcases hu with rfl | h'
      · exact hu0
      · rw [h'] at hu0; linarith
    exact (sin_half_eq_zero_iff φ).1 hsφ
  · have hsq : Real.sin (θ / 2) ^ 2 = u ^ 2 := unit_smul_sq hn hm hsv
    have hcase : u = Real.sin (θ / 2) ∨ u = -Real.sin (θ / 2) := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq.symm with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    rcases hcase with rfl | rfl
    · refine Or.inl ?_
      exact (smul_right_injective Vec3 hs0 hsv).symm
    · refine Or.inr (Or.inl ?_)
      have hsv' : Real.sin (θ / 2) • n = Real.sin (θ / 2) • (-m) := by
        rw [hsv]; module
      have hnm : n = -m := smul_right_injective Vec3 hs0 hsv'
      rw [hnm, neg_neg]

/-! ## the degenerate cross-domain class is genuinely present, and harmless -/

/-- **DERIVED (§49).**  The degenerate class is genuinely a *cross-domain* class: for
arbitrary unit directions the two identity parameters are coincident. -/
theorem degenerate_cross_coincidence {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m) :
    Coincident n (2 * Real.pi) m 0 := by
  have h1 : PhiGen n (2 * Real.pi) = PhiGen n 0 := by
    have := coincidence_add_two_pi n 0
    rwa [zero_add] at this
  have h2 : PhiGen n 0 = LinearMap.id := (coincidence_id_iff hn 0).2 ⟨0, by norm_num⟩
  have h3 : PhiGen m 0 = LinearMap.id := (coincidence_id_iff hm 0).2 ⟨0, by norm_num⟩
  rw [Coincident, h1, h2, h3]

/-- **DERIVED.**  The value of an explicit local model at the full parameter turn. -/
theorem locFam_full_turn (k : ℤ) (n : Vec3) : locFam k n (2 * Real.pi) = w1 := by
  have harg : ((k : ℝ) + 1 / 2) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) + Real.pi := by ring
  have hc : Real.cos (((k : ℝ) + 1 / 2) * (2 * Real.pi)) = -1 := by
    rw [harg]; exact Real.cos_int_mul_two_pi_add_pi k
  have hs : Real.sin (((k : ℝ) + 1 / 2) * (2 * Real.pi)) = 0 := by
    have h2 : ((k : ℝ) + 1 / 2) * (2 * Real.pi) = ((2 * k + 1 : ℤ) : ℝ) * Real.pi := by
      push_cast; ring
    rw [h2]
    exact Real.sin_int_mul_pi (2 * k + 1)
  have hz : zexp 0 ((k : ℝ) + 1 / 2) (2 * Real.pi) = -w1 := by
    rw [zexp_zero_val, hc, hs, zc]; module
  have hsq : (-w1 : W) ⋆ (-w1) = w1 := by
    have h1 : (-w1 : W) = (-1 : ℝ) • w1 := by module
    rw [h1, smul_mul_W, mul_smul_W, one_mul_W, smul_smul]
    norm_num
  rw [locFam, hz, full_turn_val, hsq]

/-- **PRINCIPAL THEOREM (§49).**  The degenerate cross-domain relation is **satisfied** by
every explicit local model, for arbitrary pairs of unit directions: it imposes no condition
beyond those already classified.  So the two cross-domain classes behave completely
differently — the antipodal one is an obstruction, the degenerate one is not. -/
theorem degenerate_relations_satisfied (k : ℤ) (n m : Vec3) :
    locFam k n (2 * Real.pi) = locFam k m 0 := by
  have hz : zexp 0 ((k : ℝ) + 1 / 2) 0 = w1 := by
    rw [zexp_zero_val, mul_zero, Real.cos_zero, Real.sin_zero, zc]; module
  rw [locFam_full_turn k n, locFam, Un_zero, mul_one_W, hz]

end NullSectorTask18
