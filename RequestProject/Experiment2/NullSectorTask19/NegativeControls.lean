import RequestProject.Experiment2.NullSectorTask19.HigherRegularity

/-!
# Task 19, Package J: negative controls and theorem-boundary audit

Each control below fixes one boundary of a Task-XIX theorem by exhibiting the failure that
occurs when a hypothesis is dropped (§82).  Nothing here is used to prove a positive
statement; the controls are endpoints in their own right.

1. `control_centrality_not_local_exactness` — centrality alone does not imply local
   exactness.
2. `control_bridge_not_global` — primitive bridge existence alone does not imply global
   exactness.
3. `control_connectedness_needed` — connectedness cannot be dropped from label rigidity.
4. `control_openness_needed` — openness cannot be dropped from open-maximality claims.
5. `control_coverage_not_relations` — direction coverage does not imply relation coverage.
6. `control_labels_not_arbitrary` — component labels are constrained.
7. `control_c1_needs_construction` — `C¹` does not automatically give `C∞`; the upgrade is a
   construction, and one further upgrade (analyticity) provably fails for that construction.
8. `control_maximality_not_canonicality` — maximality never implies canonicality.
-/

namespace NullSectorTask19

open scoped ContDiff

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## 1 — centrality alone does not imply local exactness -/

/-- **NEGATIVE CONTROL (§82.1).**  A factor may be central, normalized, multiplicative and
jointly continuous — a primitive bridge in the full Task-XIX sense — and still reconstruct a
family which is **not** locally exact.  Centrality carries no exactness information at
all. -/
theorem control_centrality_not_local_exactness :
    ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧
      (∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, c n θ ∈ Z) ∧ ¬ IsLocallyExact (recon c) := by
  have hc : IsPrimitiveBridge (cexp 0 (1 / 3)) := cexp_isPrimitiveBridge 0 (1 / 3)
  refine ⟨cexp 0 (1 / 3), hc, hc.central, fun hloc => ?_⟩
  have hrates := (recon_locallyExact_iff hc).1 hloc e1 e1_isUnitAxis
  have hb : primRateB (cexp 0 (1 / 3)) e1 = 1 / 3 := (cexp_rates 0 (1 / 3) e1_isUnitAxis).2
  rw [hb] at hrates
  obtain ⟨k, hk⟩ := hrates.2
  have h6 : (6 * k : ℤ) = -1 := by
    have : (6 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-! ## 2 — primitive bridge existence alone does not imply global exactness -/

/-- **NEGATIVE CONTROL (§82.2).**  Primitive bridges exist, and even locally exact ones; the
global statement nevertheless fails.  Existence of the primitive object is therefore not the
obstruction. -/
theorem control_bridge_not_global :
    (∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsLocallyExact (recon c)) ∧
      ¬ ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c) :=
  ⟨primitiveBridge_boundary.2.1, primitiveBridge_boundary.2.2⟩

/-! ## 3 — connectedness cannot be dropped from label rigidity -/

/-- **NEGATIVE CONTROL (§82.3).**  On a preconnected domain the label is rigid; on a
disconnected admissible domain four different labels coexist.  Connectedness is therefore
load-bearing in the rigidity theorem. -/
theorem control_connectedness_needed :
    ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValuedOn multiD U ∧
      rateBeta U e1 ≠ rateBeta U p35 := by
  obtain ⟨-, -, -, -, -, U, hU, hexact, h1, -, h3, -⟩ := multiD_admissible_four_labels
  refine ⟨U, hU, hexact, ?_⟩
  rw [h1, h3]
  norm_num

/-! ## 4 — openness cannot be dropped from open-maximality claims -/

/-- **NEGATIVE CONTROL (§82.4).**  The inherited domain `Dom e₁` is maximal in the open
preconnected admissible class but **not** maximal in the plain preconnected admissible
class, and the maximal preconnected witness `lexA` is not open.  Openness cannot be dropped
from the open-maximality statement. -/
theorem control_openness_needed :
    IsMaximalIn OpenConnAdmClass (Dom e1) ∧ ¬ IsMaximalIn PreconnAdmClass (Dom e1) ∧
      IsMaximalIn PreconnAdmClass lexA ∧ ¬ OpenDomain lexA :=
  ⟨three_maximality_notions_differ.2.2.2.1, three_maximality_notions_differ.2.2.2.2,
    three_maximality_notions_differ.1, three_maximality_notions_differ.2.2.1⟩

/-! ## 5 — direction coverage does not imply relation coverage -/

/-- **NEGATIVE CONTROL (§82.5).**  The inherited system covers every direction and has
coherent overlaps, and still fails relation completeness. -/
theorem control_coverage_not_relations :
    CoversDirections Dom ∧ CoherentOverlaps Dom inhSystem ∧
      ¬ SystemRelationComplete Dom inhSystem :=
  ⟨coverage_not_relationComplete.1, fun _ _ _ _ _ _ => rfl,
    coverage_not_relationComplete.2.2.2⟩

/-! ## 6 — component labels are not arbitrary -/

/-- **NEGATIVE CONTROL (§82.6).**  Prescribed component labels are constrained in two
independent ways: differently labelled level sets must have disjoint closures, and even
pairwise disjoint closures are not enough when the labelled directions accumulate. -/
theorem control_labels_not_arbitrary :
    (∀ (D : Set Vec3) (l : Vec3 → ℤ), LabelRealized D l → ∀ j k : ℤ, j ≠ k →
        closure (sphSet (LabelLevel D l j)) ∩ closure (sphSet (LabelLevel D l k)) = ∅) ∧
      ¬ LabelRealized accDom accLabel :=
  ⟨fun _ _ h _ _ hjk => label_levels_separated h hjk, separation_not_sufficient.2⟩

/-! ## 7 — `C¹` does not automatically give `C∞` -/

/-- **NEGATIVE CONTROL (§82.7).**  The `C∞` statement is *not* a formal consequence of the
`C¹` statement: it required proving the staircase smooth at index `∞`.  And the ladder does
stop: the exact plateau on which the construction depends is impossible for an analytic
function, so no further automatic upgrade is available. -/
theorem control_c1_needs_construction :
    (∀ N : ℕ, ContDiff ℝ ∞ (stair N)) ∧
      (∀ f : ℝ → ℝ, AnalyticOnNhd ℝ f Set.univ → ∀ p q c : ℝ, p < q →
        (∀ x ∈ Set.Ioo p q, f x = c) → ∀ x : ℝ, f x = c) :=
  ⟨stair_contDiff_infty, fun _ hf _ _ _ hpq hconst =>
    analytic_plateau_forces_constant hf hpq hconst⟩

/-! ## 8 — maximality never implies canonicality -/

/-- **NEGATIVE CONTROL (§82.8).**  Maximal admissible sets exist and are not unique;
canonicality is therefore not obtainable from maximality without an independent uniqueness
theorem, and no such theorem is available. -/
theorem control_maximality_not_canonicality :
    IsMaximalIn AdmClass flipSet ∧
      ∃ D E : Set Vec3, IsMaximalIn AdmClass D ∧ IsMaximalIn AdmClass E ∧ D ≠ E :=
  ⟨exists_maximal_adm, maximal_adm_not_unique⟩

/-! ## §83, §84 — the changed theorem boundaries, recorded formally -/

/-- **BOUNDARY RECORD (§84), maximal preconnected admissible domains.**  The intended
unconditional equivalence *inclusion-maximal preconnected admissible ↔ antipodally complete*
is **not** available.  What is proved, and bundled here so the boundary is visible, is:
antipodal completeness is sufficient; maximality implies the weaker closure-completeness
condition; and the converse holds under the explicitly named additional hypothesis
`AccessibleMissing`. -/
theorem boundary_maximal_preconnected :
    (∀ D : Set Vec3, PreconnAdmClass D → AntipodalComplete D → IsMaximalIn PreconnAdmClass D) ∧
      (∀ D : Set Vec3, IsMaximalIn PreconnAdmClass D → ∀ p : Sph, p ∈ closure (sphSet D) →
        (p : Vec3) ∈ D ∨ -(p : Vec3) ∈ D) ∧
      (∀ D : Set Vec3, IsMaximalIn PreconnAdmClass D → AccessibleMissing D →
        AntipodalComplete D) :=
  ⟨fun _ hD hc => antipodalComplete_maximal hD hc,
    fun _ hmax _ hp => maximal_closureComplete hmax hp,
    fun _ hmax hacc => maximal_antipodalComplete_of_accessible hmax hacc⟩

end NullSectorTask19
