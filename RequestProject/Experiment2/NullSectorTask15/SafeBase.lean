import RequestProject.Experiment2.NullSectorTask14.SelectionAudit
import RequestProject.Experiment2.NullSectorTask11.ContinuousClassification

/-!
# Task 15, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

* `RequestProject.Experiment2.NullSectorTask14.SelectionAudit` — the top of the *reconstruction* chain
  of Task 14 (its late comparison module `Task14.Identification` is **not** imported here
  and is unreachable from any Task-15 reconstruction module).  Through it Task 15 inherits
  the whole Task-08 → Task-14 development: the associative carrier `W` with product `⋆`,
  the exact centre `Z = spanℝ{w1, wS}` with `wS ⋆ wS = -w1`, the derived axis-generator map
  `Jmap`, the arbitrary-axis reference implementations `Un n θ`, the implemented
  automorphism family `PhiGen n θ`, the `Implements` relation, the central-defect theorem
  `implements_defect_mem_Z` and the pointwise lift classification `axis_lift_iff`.
* `RequestProject.Experiment2.NullSectorTask11.ContinuousClassification` — the one-axis classification
  of *continuous* central residual factors (`IsCentralHom`, `zexp`,
  `coeff_continuous_classification`, `centralHom_continuous_classification`), imported
  explicitly because Task 15 uses it as a **named dependency** in §III.

## Firewalls

*Reconstruction firewall.*  No physical, dynamical or representation-theoretic notion is
used or mentioned in any Task-15 reconstruction module (§II of the task): no particle, no
spin dynamics, no mass/energy/momentum/frequency, no Hamiltonian or field equation, no
electromagnetic or gravitational field, no gauge potential or connection, no projective
representation or cocycle, no conventional spin-group machinery.  The central composition
discrepancy of §IV is kept **explicit** as an element of the carrier; nothing is
quotiented and no cohomological vocabulary is used.

*Late-comparison firewall.*  The single Task-15 comparison module
`RequestProject.Experiment2.NullSectorTask15.OptionCAudit` is imported by nothing but
`RequestProject.Experiment2.NullSectorTask15.Task15`, and no reconstruction result depends on it.

## Content of this module

Bookkeeping only: the identification of the two inherited notations for a central element,
elementary invertibility bookkeeping in the centre, and the cancellation lemma for the
inherited reference implementations, which is used throughout Task 15.
-/

namespace NullSectorTask15

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14

/-! ## The two inherited notations for a central element agree -/

/-- **INHERITED (bookkeeping).**  The Task-13 notation `zz` and the Task-11 notation `zc`
denote the same element `a • 1 + b • S` of the exact centre. -/
theorem zz_eq_zc (a b : ℝ) : zz a b = zc a b := rfl

/-! ## Central units -/

/-- **NEUTRAL DEFINITION.**  An invertible element of the exact centre; its inverse is
required to be central as well (by `central_inv_mem_Z` this is automatic). -/
def IsCentralUnit (z : W) : Prop := z ∈ Z ∧ ∃ zi : W, zi ∈ Z ∧ z ⋆ zi = w1 ∧ zi ⋆ z = w1

theorem w1_mem_Z : w1 ∈ Z := by
  have := zc_mem_Z 1 0
  rwa [zc_one_zero] at this

theorem isCentralUnit_one : IsCentralUnit w1 :=
  ⟨w1_mem_Z, w1, w1_mem_Z, one_mul_W w1, one_mul_W w1⟩

theorem isCentralUnit_zc {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) : IsCentralUnit (zc a b) := by
  refine ⟨zc_mem_Z a b, NullSectorTask14.zinv a b, ?_, ?_, ?_⟩
  · exact zz_mem_Z _ _
  · exact NullSectorTask14.zz_mul_zinv hab
  · exact NullSectorTask14.zinv_mul_zz hab

theorem isCentralUnit_mul {z w : W} (hz : IsCentralUnit z) (hw : IsCentralUnit w) :
    IsCentralUnit (z ⋆ w) := by
  obtain ⟨hzZ, zi, hziZ, hz1, hz2⟩ := hz
  obtain ⟨hwZ, wi, hwiZ, hw1, hw2⟩ := hw
  refine ⟨Z_mul_mem hzZ hwZ, wi ⋆ zi, Z_mul_mem hwiZ hziZ, ?_, ?_⟩
  · calc (z ⋆ w) ⋆ (wi ⋆ zi) = (z ⋆ (w ⋆ wi)) ⋆ zi := by simp only [mul_assoc_W]
      _ = w1 := by rw [hw1, mul_one_W, hz1]
  · calc (wi ⋆ zi) ⋆ (z ⋆ w) = (wi ⋆ (zi ⋆ z)) ⋆ w := by simp only [mul_assoc_W]
      _ = w1 := by rw [hz2, mul_one_W, hw2]

/-- **DERIVED.**  A central unit written in coordinates has a nonzero coefficient pair. -/
theorem isCentralUnit_coeffs {a b : ℝ} (h : IsCentralUnit (zc a b)) : a ^ 2 + b ^ 2 ≠ 0 := by
  obtain ⟨-, zi, hziZ, h1, -⟩ := h
  intro hab
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  rw [ha, hb] at h1
  have hz0 : zc (0 : ℝ) (0 : ℝ) = 0 := by
    funext i; fin_cases i <;> simp [zc, w1, wS]
  rw [hz0, zero_mul_W] at h1
  have := congrFun h1 0
  simp [w1] at this

/-! ## Cancellation against the inherited reference implementations -/

/-- **DERIVED.**  The inherited reference implementation can be cancelled on the right. -/
theorem Un_right_cancel {n : Vec3} (hn : IsUnitAxis n) {θ : ℝ} {x y : W}
    (h : x ⋆ Un n θ = y ⋆ Un n θ) : x = y := by
  have := congrArg (fun t => t ⋆ Un n (-θ)) h
  simpa only [mul_assoc_W, Un_mul_neg hn, mul_one_W] using this

end NullSectorTask15
