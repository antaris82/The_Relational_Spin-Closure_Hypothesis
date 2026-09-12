import RequestProject.Experiment2.NullSectorTask20.NegativeControls

/-!
# Task 20, final layer: the comparison-only module (Phase B)

**COMPARISON ONLY, AND LAST.**  This module is imported by nothing but
`RequestProject.Experiment2.NullSectorTask20.Task20`.  No Task-20 reconstruction module imports it, and
no reconstruction theorem depends on it.  Phase A (Packages A–J) is complete and frozen
before this module is read; nothing here is used as an input to any Phase-A statement.

## What is formally established here

One and only one external comparison is carried out *formally*: the intrinsic internal core
carrier `Lift`, with the inherited product, is identified with the unit quaternions.  The map
and its inverse are explicit, multiplicativity is proved, and the image of the unit sphere is
proved to be exactly `Lift`.  By the standard of §90 this comparison is therefore an
**EXACT EQUIVALENCE**; every other comparison in `TASK20_AUDIT.md` is weaker and is labelled
there, not here.

## What is *not* established here

No rotation group, covering space, bundle, cocycle, cohomology class, principal object or
representation is constructed anywhere in this project, and no such identification is
claimed as a theorem.  In particular:

* the visible image is proved (Phase A) to be a group under composition with a two-element
  kernel over the core carrier, but it is **not** formally identified with any conventional
  rotation group;
* the two-element kernel is **not** presented as a covering-space fibre: no covering space
  is constructed;
* the integer relative labels are **not** called cohomological: no coefficient object,
  cochain complex, differential or class was constructed.

These restrictions are exactly the Package-L controls, and they are what the status column
of the equivalence matrix records.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

open Quaternion

/-- **COMPARISON ONLY.**  The explicit map from the quaternions to the inherited carrier. -/
noncomputable def fromQuat (q : Quaternion ℝ) : W :=
  q.re • w1 - Jmap (q.imI, q.imJ, q.imK)

/-- **COMPARISON ONLY.**  The map is unital. -/
theorem fromQuat_one : fromQuat 1 = w1 := by
  simp only [fromQuat, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
    Quaternion.imK_one, one_smul]
  have : Jmap ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := Jmap_zero
  rw [this, sub_zero]

/-- **COMPARISON ONLY.**  The map is multiplicative: the inherited product restricted to the
image is exactly quaternion multiplication. -/
theorem fromQuat_mul (q p : Quaternion ℝ) : fromQuat (q * p) = fromQuat q ⋆ fromQuat p := by
  rw [fromQuat, fromQuat, fromQuat, quat_mul]
  have hre : (q * p).re
      = q.re * p.re - h3 (q.imI, q.imJ, q.imK) (p.imI, p.imJ, p.imK) := by
    simp only [Quaternion.re_mul, h3, dot3]
    ring
  have him : ((q * p).imI, (q * p).imJ, (q * p).imK)
      = q.re • (p.imI, p.imJ, p.imK) + p.re • (q.imI, q.imJ, q.imK)
        + spCross (q.imI, q.imJ, q.imK) (p.imI, p.imJ, p.imK) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, spCross,
        Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  rw [hre, him]

/-- **COMPARISON ONLY.**  The map is injective. -/
theorem fromQuat_injective : Function.Injective fromQuat := by
  intro q p h
  have h0 := congrFun h 0
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  simp only [fromQuat, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, w1, Jmap_coord_0,
    Jmap_coord_4, Jmap_coord_5, Jmap_coord_6] at h0 h4 h5 h6
  simp at h0 h4 h5 h6
  refine Quaternion.ext (a := q) (b := p) ?_ ?_ ?_ ?_ <;> linarith

/-- **COMPARISON ONLY, EXACT EQUIVALENCE.**  The internal core carrier is exactly the image
of the unit quaternions, the map is injective, unital and multiplicative.  This is the only
external identification proved formally in this project. -/
theorem lift_eq_image_unit_quaternions :
    Lift = fromQuat '' {q : Quaternion ℝ | Quaternion.normSq q = 1} := by
  ext u
  constructor
  · rintro ⟨a, v, ha, rfl⟩
    refine ⟨⟨a, v.1, v.2.1, v.2.2⟩, ?_, ?_⟩
    · show Quaternion.normSq ⟨a, v.1, v.2.1, v.2.2⟩ = 1
      rw [Quaternion.normSq_def']
      simp only [h3, dot3] at ha
      simp only []
      nlinarith [ha]
    · rw [fromQuat]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.re, (q.imI, q.imJ, q.imK), ?_, rfl⟩
    have hn : Quaternion.normSq q = 1 := hq
    rw [Quaternion.normSq_def'] at hn
    simp only [h3, dot3]
    nlinarith [hn]

/-- **COMPARISON ONLY.**  The collected Phase-A statements against which the comparison in
`TASK20_AUDIT.md` is made.  Every component is an already-proved Task-20 reconstruction
theorem; this module adds nothing to them. -/
theorem comparison_phaseA_summary :
    (∀ u : W, u ∈ Lift ↔ ∃ (n : Vec3) (θ : ℝ), IsUnitAxis n ∧ u = Un n θ) ∧
      {u : W | u ∈ Lift ∧ proj u = LinearMap.id} = ({w1, -w1} : Set W) ∧
      {u : W | u ∈ LiftZ ∧ proj u = LinearMap.id} = CentreOf LiftZ ∧
      (¬ ∃ σ : VisParam → W, Continuous σ ∧ (∀ p : VisParam, σ p ∈ Lift) ∧
        (∀ p : VisParam, proj (σ p) = visMap p) ∧
        (∀ p q : VisParam, visRel p q → σ p = σ q)) :=
  ⟨mem_Lift_iff_exists_Un, kernel_core, kernel_vs_centre.1,
    no_continuous_quotient_compatible_lift⟩

end NullSectorTask20
