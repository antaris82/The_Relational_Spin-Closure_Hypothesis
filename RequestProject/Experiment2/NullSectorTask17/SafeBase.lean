import RequestProject.Experiment2.NullSectorTask16.LocalRepair

/-!
# Task 17, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

* `RequestProject.Experiment2.NullSectorTask16.LocalRepair` — the *strongest reconstruction layer* of
  Task 16.  Through it Task 17 inherits, and only through it:

  * the associative carrier `W` with product `⋆`, unit `w1`, exact centre `Z`, the
    inherited spatial carrier `Vec3` with the inherited form `h3`, the unit directions
    `IsUnitAxis`, the reference implementations `Un n θ`, the visible family `PhiGen n θ`;
  * the Task-16 exact coincidence relation `coincidence_iff`, `coincidence_iff_coords`;
  * the Task-16 joint-regularity class `IsJointlyRegularFamily` with its classification
    `jointRegularity_classification` and the continuity of the two recovered rates;
  * the Task-16 global obstruction `no_global_jointly_regular_transformationValued`;
  * the Task-16 sign-relaxed class `IsSignTransformationValued` and its uniqueness
    `signValued_eq_reference`;
  * the Task-16 local layer: `Dom`, `IsTransformationValuedOn`, `locFam`, `local_rates`,
    `locFam_transformationValuedOn`, `locFam_overlap`.

**No Task-16 `Identification` or `OptionCAudit` (comparison) module is reachable from any
Task-17 reconstruction module.**  The only Task-17 comparison module,
`RequestProject.Experiment2.NullSectorTask17.Identification`, is imported by nothing but
`RequestProject.Experiment2.NullSectorTask17.Task17`.

## Firewalls

*Reconstruction firewall.*  No conventional geometric or topological target is imported or
used anywhere in the Task-17 reconstruction modules: no rotation or double-cover group, no
spinor, no covering space, no bundle of any kind, no Čech data, no cocycle or cohomology,
no projective representation, no classification theorem for sphere bundles.  Every notion
below is defined from the inherited carrier, the inherited unit directions and the
inherited visible family.  The words `open`, `connected`, `path` are used in their bare
point-set sense for the inherited subspace of unit directions, and every such property is
*proved intrinsically* — no standard hemisphere or sphere theorem is imported.

*Physical firewall.*  No physical notion of any kind occurs in a Task-17 reconstruction
statement.

## Content of this module

Bookkeeping only:

* the normalization map of the inherited spatial carrier and its elementary identities;
* the straight-line-through-normalization path between unit directions;
* the elementary rigidity lemma for continuous functions with values in `ℤ + 1/2` on a
  preconnected set, proved from the intermediate value property alone.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## The inherited form in coordinates -/

theorem h3_self_coord (w : Vec3) : h3 w w = w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 := by
  simp only [h3, dot3]; ring

theorem h3_self_nonneg (w : Vec3) : 0 ≤ h3 w w := by
  rw [h3_self_coord]; positivity

theorem h3_self_eq_zero_iff (w : Vec3) : h3 w w = 0 ↔ w = 0 := by
  constructor
  · intro h
    rw [h3_self_coord] at h
    have h1 : w.1 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2.1, sq_nonneg w.2.2]
    have h2 : w.2.1 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2.1, sq_nonneg w.2.2]
    have h3' : w.2.2 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2.1, sq_nonneg w.2.2]
    exact Prod.ext h1 (Prod.ext h2 h3')
  · rintro rfl; simp [h3, dot3]

theorem h3_self_pos {w : Vec3} (hw : w ≠ 0) : 0 < h3 w w :=
  lt_of_le_of_ne (h3_self_nonneg w) (fun h => hw ((h3_self_eq_zero_iff w).1 h.symm))

theorem h3_comm (v w : Vec3) : h3 v w = h3 w v := by
  simp only [h3, dot3]; ring

theorem h3_smul_left (c : ℝ) (v w : Vec3) : h3 (c • v) w = c * h3 v w := by
  simp only [h3, dot3, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem h3_add_left (u v w : Vec3) : h3 (u + v) w = h3 u w + h3 v w := by
  simp only [h3, dot3, Prod.fst_add, Prod.snd_add]; ring

/-! ## Normalization -/

/-- **NEUTRAL DEFINITION.**  The inherited length of a spatial vector. -/
noncomputable def nrm (w : Vec3) : ℝ := Real.sqrt (h3 w w)

theorem nrm_pos {w : Vec3} (hw : w ≠ 0) : 0 < nrm w := Real.sqrt_pos.2 (h3_self_pos hw)

theorem nrm_sq (w : Vec3) : nrm w ^ 2 = h3 w w := Real.sq_sqrt (h3_self_nonneg w)

/-- **NEUTRAL DEFINITION.**  The normalization of a nonzero spatial vector. -/
noncomputable def nrmz (w : Vec3) : Vec3 := (nrm w)⁻¹ • w

theorem nrmz_isUnitAxis {w : Vec3} (hw : w ≠ 0) : IsUnitAxis (nrmz w) := by
  have hp := nrm_pos hw
  have hs : nrm w ^ 2 = h3 w w := nrm_sq w
  rw [IsUnitAxis, nrmz, h3_smul_left, h3_comm, h3_smul_left, h3_comm]
  field_simp
  nlinarith [hs, hp]

theorem h3_nrmz_left (w v : Vec3) : h3 (nrmz w) v = (nrm w)⁻¹ * h3 w v := by
  rw [nrmz, h3_smul_left]

theorem nrmz_pos_iff {w : Vec3} (hw : w ≠ 0) (v : Vec3) :
    0 < h3 (nrmz w) v ↔ 0 < h3 w v := by
  rw [h3_nrmz_left]
  have hp : 0 < (nrm w)⁻¹ := inv_pos.2 (nrm_pos hw)
  constructor
  · intro h; nlinarith [h, hp]
  · intro h; positivity

theorem nrmz_of_isUnitAxis {n : Vec3} (hn : IsUnitAxis n) : nrmz n = n := by
  have hnn : h3 n n = 1 := hn
  rw [nrmz, nrm, hnn, Real.sqrt_one, inv_one, one_smul]

theorem isUnitAxis_ne_zero {n : Vec3} (hn : IsUnitAxis n) : n ≠ 0 := by
  intro h
  have hnn : h3 n n = 1 := hn
  rw [h] at hnn
  simp [h3, dot3] at hnn

/-! ## The straight-line path between unit directions -/

/-- **NEUTRAL DEFINITION.**  The inherited straight-line interpolation of two spatial
directions. -/
def segLin (n₀ n₁ : Vec3) (t : ℝ) : Vec3 := (1 - t) • n₀ + t • n₁

/-- **NEUTRAL DEFINITION.**  The straight-line interpolation of two directions, normalized
back to the unit directions. -/
noncomputable def segPath (n₀ n₁ : Vec3) (t : ℝ) : Vec3 := nrmz (segLin n₀ n₁ t)

@[simp] theorem segLin_zero (n₀ n₁ : Vec3) : segLin n₀ n₁ 0 = n₀ := by
  simp [segLin]

@[simp] theorem segLin_one (n₀ n₁ : Vec3) : segLin n₀ n₁ 1 = n₁ := by
  simp [segLin]

theorem h3_segLin_left (n₀ n₁ v : Vec3) (t : ℝ) :
    h3 (segLin n₀ n₁ t) v = (1 - t) * h3 n₀ v + t * h3 n₁ v := by
  rw [segLin, h3_add_left, h3_smul_left, h3_smul_left]

theorem continuous_segLin (n₀ n₁ : Vec3) : Continuous (segLin n₀ n₁) := by
  unfold segLin
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

theorem continuous_h3_left (v : Vec3) : Continuous fun w : Vec3 => h3 w v := by
  simp only [h3, dot3]
  fun_prop

theorem continuousOn_nrmz_comp {f : ℝ → Vec3} (hf : Continuous f) {s : Set ℝ}
    (hne : ∀ t ∈ s, f t ≠ 0) : ContinuousOn (fun t => nrmz (f t)) s := by
  have hsq : Continuous fun t => h3 (f t) (f t) := by
    simp only [h3, dot3]
    fun_prop
  have hn : ContinuousOn (fun t => nrm (f t)) s :=
    (Real.continuous_sqrt.comp hsq).continuousOn
  have hinv : ContinuousOn (fun t => (nrm (f t))⁻¹) s :=
    hn.inv₀ fun t ht => ne_of_gt (nrm_pos (hne t ht))
  exact hinv.smul hf.continuousOn

theorem segPath_isUnitAxis {n₀ n₁ : Vec3} {t : ℝ} (h : segLin n₀ n₁ t ≠ 0) :
    IsUnitAxis (segPath n₀ n₁ t) := nrmz_isUnitAxis h

theorem segPath_zero {n₀ n₁ : Vec3} (h : IsUnitAxis n₀) : segPath n₀ n₁ 0 = n₀ := by
  rw [segPath, segLin_zero, nrmz_of_isUnitAxis h]

theorem segPath_one {n₀ n₁ : Vec3} (h : IsUnitAxis n₁) : segPath n₀ n₁ 1 = n₁ := by
  rw [segPath, segLin_one, nrmz_of_isUnitAxis h]

/-! ## Rigidity of continuous half-odd-valued functions -/

/-- **DERIVED.**  A real number cannot be simultaneously of the form `k + 1/2` and an
integer. -/
theorem not_int_and_halfodd {x : ℝ} (k j : ℤ) (h1 : x = (k : ℝ) + 1 / 2) (h2 : x = (j : ℝ)) :
    False := by
  have h : (2 * j : ℤ) = 2 * k + 1 := by
    have : (2 * (j : ℝ)) = 2 * (k : ℝ) + 1 := by rw [← h2, h1]; ring
    exact_mod_cast this
  omega

/-- **DERIVED (intrinsic rigidity).**  A continuous real function whose values on a
preconnected set all lie in `ℤ + 1/2` is constant on that set.  Only the intermediate value
property is used; no discreteness theorem is imported. -/
theorem halfodd_const_of_preconnected {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : IsPreconnected D) {f : X → ℝ} (hf : ContinuousOn f D)
    (hint : ∀ x ∈ D, ∃ k : ℤ, f x = (k : ℝ) + 1 / 2) :
    ∀ x ∈ D, ∀ y ∈ D, f x = f y := by
  intro x hx y hy
  obtain ⟨kx, hkx⟩ := hint x hx
  obtain ⟨ky, hky⟩ := hint y hy
  rcases lt_trichotomy kx ky with hlt | heq | hgt
  · exfalso
    have hstep : (kx : ℝ) + 1 ≤ (ky : ℝ) := by exact_mod_cast hlt
    have hmem : (kx : ℝ) + 1 ∈ Set.Icc (f x) (f y) := by
      rw [hkx, hky]; constructor <;> linarith
    obtain ⟨z, hz, hfz⟩ := hD.intermediate_value hx hy hf hmem
    obtain ⟨kz, hkz⟩ := hint z hz
    exact not_int_and_halfodd kz (kx + 1) hkz (by rw [hfz]; push_cast; ring)
  · rw [hkx, hky, heq]
  · exfalso
    have hstep : (ky : ℝ) + 1 ≤ (kx : ℝ) := by exact_mod_cast hgt
    have hmem : (ky : ℝ) + 1 ∈ Set.Icc (f y) (f x) := by
      rw [hkx, hky]; constructor <;> linarith
    obtain ⟨z, hz, hfz⟩ := hD.intermediate_value hy hx hf hmem
    obtain ⟨kz, hkz⟩ := hint z hz
    exact not_int_and_halfodd kz (ky + 1) hkz (by rw [hfz]; push_cast; ring)

end NullSectorTask17
