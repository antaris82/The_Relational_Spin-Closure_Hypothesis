import RequestProject.Experiment2.NullSectorTask19.NegativeControls

/-!
# Task 20, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The single import is `RequestProject.Experiment2.NullSectorTask19.NegativeControls`, the last
*reconstruction* module of Task 19.  Through it, and only through it, Task 20 inherits the
complete Task-19 reconstruction development and, transitively, the reconstruction layers of
Tasks 1–18:

* the associative carrier `W` with product `⋆`, unit `w1`, the exact centre `Z`, the central
  normal form `zc`, the central one-parameter elements `zexp`;
* the spatial carrier `Vec3`, the inherited form `h3`, the unit directions `IsUnitAxis`, the
  inherited subspace `Sph` of unit directions, the axis-to-generator map `Jmap` with its
  exact product rule, the reference implementers `Un`, the visible family `PhiGen`;
* the exact visible coincidence classification `coincidence_iff`, `SignRelated`;
* the local layer `Dom`, `refFam`, `ovl`, `Bridge`, `IsPrimitiveBridge`, `primRateA`,
  `primRateB`, `IsHalfOdd`, the three rate conditions `RateCont`, `RateHalfOdd`, `RateRev`,
  the reversal map `negSph`, and all their proved properties.

**Reconstruction firewall.**  `RequestProject.Experiment2.NullSectorTask19.Identification` — the only
comparison module of Task 19 — is *not* imported here, nor by any other Task-20
reconstruction module; neither is `RequestProject.Experiment2.NullSectorTask19.Task19` (which imports
it).  The single Task-20 comparison module,
`RequestProject.Experiment2.NullSectorTask20.Identification`, is imported by nothing but
`RequestProject.Experiment2.NullSectorTask20.Task20`.

No conventional target is named or used anywhere in the Task-20 reconstruction modules.
All Phase-A objects carry neutral names.  No physical vocabulary occurs in any
reconstruction statement.

## Content of this module

Bookkeeping only:

* the full-turn and double-full-turn values of the reference implementers;
* joint continuity of the reference implementers;
* compactness of the inherited subspace `Sph` of unit directions;
* the elementary reversal lemma: a continuous real function on `Sph` which is odd under
  reversal has a zero.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## Full turns -/

/-- **DERIVED.**  At parameter `2π` every reference implementer equals the negative of the
unit.  No unitarity of the direction is needed. -/
theorem Un_two_pi (n : Vec3) : Un n (2 * Real.pi) = -w1 := by
  have h : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [Un, h, Real.cos_pi, Real.sin_pi]
  module

/-- **DERIVED.**  At parameter `4π` every reference implementer equals the unit. -/
theorem Un_four_pi (n : Vec3) : Un n (4 * Real.pi) = w1 := by
  have h : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [Un, h, Real.cos_two_pi, Real.sin_two_pi]
  module

/-- **DERIVED.**  Shifting the parameter by `2π` flips the sign of the reference
implementer. -/
theorem Un_add_two_pi (n : Vec3) (θ : ℝ) : Un n (θ + 2 * Real.pi) = -(Un n θ) := by
  have h : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  rw [Un, Un, h, Real.cos_add_pi, Real.sin_add_pi]
  module

/-! ## Continuity -/

/-- **DERIVED.**  The reference implementers depend continuously on the pair (direction,
parameter). -/
theorem continuous_Un : Continuous fun p : Vec3 × ℝ => Un p.1 p.2 := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp only [Un, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, w1] <;> simp <;> fun_prop

/-- **DERIVED.**  Continuity of the reference implementers along continuous data. -/
theorem continuous_Un_comp {X : Type*} [TopologicalSpace X] {f : X → Vec3} {g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => Un (f x) (g x) := by
  have hf1 : Continuous fun x => (f x).1 := continuous_fst.comp hf
  have hf2 : Continuous fun x => (f x).2.1 := continuous_fst.comp (continuous_snd.comp hf)
  have hf3 : Continuous fun x => (f x).2.2 := continuous_snd.comp (continuous_snd.comp hf)
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp only [Un, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, w1] <;> simp <;>
    fun_prop

/-! ## Compactness of the inherited subspace of unit directions -/

theorem isCompact_unitSet : IsCompact {n : Vec3 | IsUnitAxis n} := by
  have hclosed : IsClosed {n : Vec3 | IsUnitAxis n} := by
    have hpre : {n : Vec3 | IsUnitAxis n} = (fun n : Vec3 => h3 n n) ⁻¹' {1} := rfl
    rw [hpre]
    refine IsClosed.preimage ?_ isClosed_singleton
    simp only [h3, dot3]
    fun_prop
  have hbdd : Bornology.IsBounded {n : Vec3 | IsUnitAxis n} := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : Vec3)]
    refine ⟨2, fun n hn => ?_⟩
    have hu : n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
      have hnn : h3 n n = 1 := hn
      simp only [h3, dot3] at hnn
      nlinarith [hnn]
    have h1 : |n.1| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg n.2.1, sq_nonneg n.2.2, sq_nonneg (n.1 - 1),
        sq_nonneg (n.1 + 1)]
    have h2 : |n.2.1| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg n.1, sq_nonneg n.2.2, sq_nonneg (n.2.1 - 1),
        sq_nonneg (n.2.1 + 1)]
    have h3' : |n.2.2| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg n.1, sq_nonneg n.2.1, sq_nonneg (n.2.2 - 1),
        sq_nonneg (n.2.2 + 1)]
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖n‖ = max |n.1| (max |n.2.1| |n.2.2|) := by
      simp [Prod.norm_def, Real.norm_eq_abs]
    rw [hnorm]
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

instance instCompactSph : CompactSpace Sph :=
  isCompact_iff_compactSpace.mp isCompact_unitSet

/-! ## The elementary reversal lemma -/

/-- **DERIVED.**  A continuous real function on the inherited subspace of unit directions
which is odd under reversal takes the value zero somewhere.  This is the elementary
obstruction underlying every later nonexistence statement: it uses *only* preconnectedness
of the direction carrier and the involution — no discreteness whatsoever. -/
theorem exists_zero_of_odd {f : Sph → ℝ} (hf : Continuous f)
    (hodd : ∀ s : Sph, f (negSph s) = -f s) : ∃ s : Sph, f s = 0 := by
  let s : Sph := ⟨e1, e1_isUnitAxis⟩
  rcases le_total 0 (f s) with h | h
  · have hmem : (0 : ℝ) ∈ Set.Icc (f (negSph s)) (f s) := by
      rw [hodd s]; exact ⟨by linarith, h⟩
    obtain ⟨t, ht⟩ := intermediate_value_univ (negSph s) s hf hmem
    exact ⟨t, ht⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (f s) (f (negSph s)) := by
      rw [hodd s]; exact ⟨h, by linarith⟩
    obtain ⟨t, ht⟩ := intermediate_value_univ s (negSph s) hf hmem
    exact ⟨t, ht⟩

end NullSectorTask20
