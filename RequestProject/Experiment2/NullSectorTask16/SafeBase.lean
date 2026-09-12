import RequestProject.Experiment2.NullSectorTask15.Infinitesimal

/-!
# Task 16, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

* `RequestProject.Experiment2.NullSectorTask15.Infinitesimal` — the top of the *reconstruction* chain
  of Task 15 that Task 16 actually needs.  Through it Task 16 inherits the whole
  Task-08 → Task-15 development:

  * the associative carrier `W` with product `⋆`, unit `w1`, and its exact centre
    `Z = spanℝ{w1, wS}` with `wS ⋆ wS = -w1` (`center_eq_Z`, `mem_Z_iff`, `Z_central`);
  * the inherited old spatial carrier `Vec3`, the positive spatial form `h3`, the
    embedding `spat`, and the derived axis-generator map `Jmap`;
  * the unit spatial directions `IsUnitAxis`;
  * the arbitrary-axis reference implementations `Un n θ`, their group law `Un_group`,
    and the implemented automorphism family `PhiGen n θ`;
  * `Implements`, `Un_implements`, `implements_defect_mem_Z`,
    `implements_defect_factor`;
  * the one-axis lift classes `IsAxisLift`, `IsContinuousAxisLift`, the exact
    factorization `axisLift_iff` and the exact continuous classification
    `continuousAxisLift_classification` with its uniqueness
    `continuousAxisLift_parameters_unique`;
  * the exponential-rotation central family `zexp α β θ` and its injectivity
    `zexp_injective`;
  * the Task-15 regular family class `IsRegularFamily`, the recovered rates
    `rateAlpha`, `rateBeta`, and the Task-15 necessary consequences of
    transformation-valuedness (`autValued_forces_alpha_zero`,
    `autValued_forces_beta_half_odd`, `autValued_antipodal_odd`);
  * the Task-15 central composition discrepancy `cdisc` and its laws.

**No `Identification` (late comparison) module of any earlier task is reachable from any
Task-16 reconstruction module.**

## Firewalls

*Reconstruction firewall.*  No conventional global construction is imported or used: no
rotation group, no unitary or double-cover group, no quaternion or matrix reconstruction
tool, no projective representation, no cocycle or cohomological vocabulary, no
covering-space or fundamental-group argument, no bundle/connection/holonomy language, and
no physical notion whatsoever.  Every statement below is about the inherited carrier `W`,
the inherited unit directions, and the inherited automorphism family `PhiGen`.

*Late-comparison firewall.*  The single Task-16 comparison module
`RequestProject.Experiment2.NullSectorTask16.Identification` is imported by nothing but
`RequestProject.Experiment2.NullSectorTask16.Task16`, and no reconstruction result depends on it.

## Content of this module

Bookkeeping only: coordinates of the inherited reference implementations, the parameter
reflection identity, and the elementary facts about unit directions that the joint
analysis needs.
-/

namespace NullSectorTask16

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15

/-! ## Coordinates of the inherited reference implementation -/

@[simp] theorem Un_coord_0 (n : Vec3) (θ : ℝ) : Un n θ 0 = Real.cos (θ / 2) := by
  simp [Un, w1]

@[simp] theorem Un_coord_7 (n : Vec3) (θ : ℝ) : Un n θ 7 = 0 := by
  simp [Un, w1]

@[simp] theorem Un_coord_1 (n : Vec3) (θ : ℝ) : Un n θ 1 = 0 := by simp [Un, w1]
@[simp] theorem Un_coord_2 (n : Vec3) (θ : ℝ) : Un n θ 2 = 0 := by simp [Un, w1]
@[simp] theorem Un_coord_3 (n : Vec3) (θ : ℝ) : Un n θ 3 = 0 := by simp [Un, w1]

@[simp] theorem Un_coord_4 (n : Vec3) (θ : ℝ) : Un n θ 4 = -(Real.sin (θ / 2) * n.2.2) := by
  simp [Un, w1]

@[simp] theorem Un_coord_5 (n : Vec3) (θ : ℝ) : Un n θ 5 = Real.sin (θ / 2) * n.2.1 := by
  simp [Un, w1]

@[simp] theorem Un_coord_6 (n : Vec3) (θ : ℝ) : Un n θ 6 = -(Real.sin (θ / 2) * n.1) := by
  simp [Un, w1]

/-- **DERIVED (bookkeeping).**  The reference implementations of `θ` and `-θ` add up to a
multiple of the unit; consequently one determines the other. -/
theorem Un_add_Un_neg (n : Vec3) (θ : ℝ) :
    Un n θ + Un n (-θ) = (2 * Real.cos (θ / 2)) • w1 := by
  rw [Un, Un_neg]; module

theorem Un_neg_eq (n : Vec3) (θ : ℝ) :
    Un n (-θ) = (2 * Real.cos (θ / 2)) • w1 - Un n θ :=
  eq_sub_of_add_eq' (Un_add_Un_neg n θ)

/-! ## Unit directions: the elementary facts used later -/

theorem isUnitAxis_iff (n : Vec3) : IsUnitAxis n ↔ n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
  simp only [IsUnitAxis, h3, dot3_apply]
  constructor <;> intro h <;> nlinarith [h]

/-- **DERIVED.**  Two unit directions related by a scalar proportion have equal squared
scalars. -/
theorem unit_smul_sq {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m) {s t : ℝ}
    (h : s • n = t • m) : s ^ 2 = t ^ 2 := by
  have hn' := (isUnitAxis_iff n).1 hn
  have hm' := (isUnitAxis_iff m).1 hm
  have h1 : s * n.1 = t * m.1 := by simpa using congrArg Prod.fst h
  have h2 : s * n.2.1 = t * m.2.1 := by simpa using congrArg (fun v : Vec3 => v.2.1) h
  have h3' : s * n.2.2 = t * m.2.2 := by simpa using congrArg (fun v : Vec3 => v.2.2) h
  linear_combination (s * n.1 + t * m.1) * h1 + (s * n.2.1 + t * m.2.1) * h2
    + (s * n.2.2 + t * m.2.2) * h3' - s ^ 2 * hn' + t ^ 2 * hm'

/-- **DERIVED.**  A scalar multiple of a unit direction vanishes only for the zero
scalar. -/
theorem smul_unit_eq_zero {n : Vec3} (hn : IsUnitAxis n) {s : ℝ} (h : s • n = 0) : s = 0 := by
  have h' : s • n = (0 : ℝ) • n := by rw [h, zero_smul]
  have := unit_smul_sq hn hn h'
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using this)

/-- **DERIVED.**  Scalar multiples of a unit direction are distinct. -/
theorem smul_unit_inj {n : Vec3} (hn : IsUnitAxis n) {s t : ℝ} (h : s • n = t • n) :
    s = t := by
  have : (s - t) • n = 0 := by rw [sub_smul, h, sub_self]
  have := smul_unit_eq_zero hn this
  linarith

/-- **DERIVED.**  If the common scalar is nonzero, the two unit directions agree. -/
theorem unit_eq_of_smul {n m : Vec3} {s t : ℝ} (hs : s ≠ 0) (h : s • n = t • m) :
    n = (t / s) • m := by
  have := congrArg (fun v : Vec3 => (s⁻¹ : ℝ) • v) h
  simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  rw [this]
  congr 1
  field_simp

end NullSectorTask16
