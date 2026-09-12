import RequestProject.Experiment2.NullSectorTask23.OldDomains

/-!
# Task 23, Packages I and J: the old bridges and the integer labels

**RECONSTRUCTION LAYER.**

Two strictly separated situations (item 73):

* **core projection.**  Two representatives that lie in the *core* carrier and have the same
  visible image differ by a kernel sign, and by nothing else (item 71): the core-exact
  overlap bridge reduces exactly to `{+1,-1}`.
* **extended projection.**  For representatives in the larger carrier the relative factor
  ranges over the whole invertible centre: an explicit central element which is neither `+1`
  nor `-1` is invisible to the projection, and the kernel even contains a continuous
  one-parameter family (items 72, 74).  The old locally exact families are of this second
  kind: an explicit one of them is shown *not* to lie in the core carrier.

Package J locates the integer labels.  The exact map `ℤ → {+1,-1}` induced by full-turn
evaluation is computed **twice**, and the two answers differ:

* on the *parameter* side the full-turn shift acts on the core carrier by `(-1)^k`, which is
  precisely parity reduction (items 76, 77);
* on the *central label* side the full-turn value of an integer label difference is `+1` for
  every integer, and the label is invisible to the core projection altogether: this is
  exactly the integer information that disappears (items 78, 79).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## Package I, core case (items 69–71) -/

/-- **PACKAGE I (item 71), principal.**  Two core representatives of the same visible element
differ by exactly one kernel sign: after imposing the certified core projection, the relative
factor of two core-exact representatives is exactly an element of `{+1,-1}`. -/
theorem core_relative_factor (u v : LiftT) (h : pr u = pr v) : ∃! e : Sgn, v = sact e u := by
  obtain ⟨e, he⟩ := (pr_eq_iff u v).1 h
  refine ⟨e, he, fun f hf => ?_⟩
  exact sact_injective_sign u (hf ▸ he)

/-! ## Package I, extended case (items 72–74) -/

theorem wS_eq_zc : (wS : W) = zc 0 1 := by
  rw [zc]
  module

theorem wS_mem_CUnit : (wS : W) ∈ CUnit := ⟨0, 1, by norm_num, wS_eq_zc⟩

theorem wS_ne_w1 : (wS : W) ≠ w1 := by
  intro h
  rw [wS_eq_zc, ← zc_one_zero] at h
  have := (zc_injective h).1
  norm_num at this

theorem wS_ne_neg_w1 : (wS : W) ≠ -w1 := by
  intro h
  have hneg : (-w1 : W) = zc (-1) 0 := by rw [zc]; module
  rw [wS_eq_zc, hneg] at h
  have := (zc_injective h).1
  norm_num at this

/-- **PACKAGE I (item 72).**  An explicit central factor which is invisible to the certified
projection and is **not** a kernel sign: in the extended carrier the relative factor of two
representatives is not confined to `{+1,-1}`. -/
theorem extended_relative_factor_not_sign :
    (wS : W) ∈ CUnit ∧ (∀ u : W, IsInvertible u → proj (wS ⋆ u) = proj u) ∧
      (wS : W) ≠ w1 ∧ (wS : W) ≠ -w1 :=
  ⟨wS_mem_CUnit, fun _ hu => proj_central_mul wS_mem_CUnit hu, wS_ne_w1, wS_ne_neg_w1⟩

/-- **PACKAGE I.**  Multiplying a core element by that central factor leaves the core
carrier: the extended relative factor is genuinely outside the core structure. -/
theorem wS_mul_notMem_Lift {u : W} (hu : u ∈ Lift) : wS ⋆ u ∉ Lift := by
  intro hmem
  have hc : conjW u ∈ Lift := conjW_mem_Lift hu
  have hprod : (wS ⋆ u) ⋆ conjW u ∈ Lift := Lift_mul_mem hmem hc
  rw [mul_assoc_W, mul_conjW hu, mul_one_W] at hprod
  rcases CUnit_inter_Lift wS_mem_CUnit hprod with h | h
  · exact wS_ne_w1 h
  · exact wS_ne_neg_w1 h

theorem labelBridge_mem_CUnit (b θ : ℝ) : labelBridge b θ ∈ CUnit := by
  refine ⟨Real.cos (b * θ), Real.sin (b * θ), ?_, labelBridge_eq b θ⟩
  rintro ⟨hc, hs⟩
  have h := Real.sin_sq_add_cos_sq (b * θ)
  rw [hc, hs] at h
  norm_num at h

theorem locFam_eq_labelBridge (k : ℤ) (n : Vec3) (θ : ℝ) :
    locFam k n θ = labelBridge ((k : ℝ) + 1 / 2) θ ⋆ Un n θ := rfl

/-- **PACKAGE I.**  The old locally exact families are representatives of the visible element
*through the extended projection*: their central factor is invisible. -/
theorem proj_locFam (k : ℤ) {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    proj (locFam k n θ) = PhiGen n θ := by
  rw [locFam_eq_labelBridge, proj_central_mul (labelBridge_mem_CUnit _ _)
    (isInvertible_of_mem_Lift (Un_mem_Lift hn θ)), proj_Un hn]

/-- **PACKAGE I (item 70).**  An explicit old locally exact representative which is **not** a
core element: what survives of the old bridge after imposing the certified core projection is
only its class, not the representative itself. -/
theorem locFam_notMem_Lift {n : Vec3} (hn : IsUnitAxis n) :
    locFam 0 n Real.pi ∉ Lift := by
  have hb : labelBridge (((0 : ℤ) : ℝ) + 1 / 2) Real.pi = wS := by
    rw [labelBridge_eq]
    have harg : (((0 : ℤ) : ℝ) + 1 / 2) * Real.pi = Real.pi / 2 := by push_cast; ring
    rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two, wS_eq_zc]
  rw [locFam_eq_labelBridge, hb]
  exact wS_mul_notMem_Lift (Un_mem_Lift hn Real.pi)

/-- **PACKAGE I (item 74).**  The kernel of the extended projection is not discrete: it
contains a continuous injective one-parameter family.  The discrete local structure of the
core projection must therefore not be read off the extended one. -/
theorem extended_kernel_continuum :
    Continuous (fun t : ℝ => zexp 1 0 t) ∧ Function.Injective (fun t : ℝ => zexp 1 0 t) ∧
      ∀ t : ℝ, zexp 1 0 t ∈ CUnit ∧ proj (zexp 1 0 t) = LinearMap.id :=
  kernel_full_continuum

/-! ## Package J: the parity map (items 75–77) -/

/-- The multiplicative comparison map of the sign carrier with the reals. -/
def sgnHom : Sgn →* ℝ where
  toFun e := (e : ℝ)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **NEUTRAL DEFINITION (item 76).**  The map from integers to kernel signs. -/
def parityMap (k : ℤ) : Sgn := Sgn.negOne ^ k

theorem parityMap_val (k : ℤ) : ((parityMap k : Sgn) : ℝ) = (-1 : ℝ) ^ k := by
  have h : sgnHom (Sgn.negOne ^ k) = (sgnHom Sgn.negOne) ^ k := map_zpow sgnHom _ _
  simpa [sgnHom, parityMap] using h

theorem parityMap_mul (k l : ℤ) : parityMap (k + l) = parityMap k * parityMap l := by
  rw [parityMap, parityMap, parityMap, zpow_add]

/-- **PACKAGE J (item 77).**  The map is precisely parity reduction. -/
theorem parityMap_eq_one_iff (k : ℤ) : parityMap k = 1 ↔ Even k := by
  constructor
  · intro h
    by_contra hodd
    have hk : Odd k := Int.not_even_iff_odd.1 hodd
    have hval : ((parityMap k : Sgn) : ℝ) = -1 := by
      rw [parityMap_val, hk.neg_one_zpow]
    rw [h] at hval
    norm_num at hval
  · intro h
    refine Subtype.ext ?_
    rw [parityMap_val, h.neg_one_zpow, Sgn.one_val]

theorem parityMap_surjective : Function.Surjective parityMap := by
  intro e
  rcases Sgn.eq_one_or_negOne e with rfl | rfl
  · exact ⟨0, (parityMap_eq_one_iff 0).2 (by decide)⟩
  · refine ⟨1, ?_⟩
    refine Subtype.ext ?_
    rw [parityMap_val, Sgn.negOne_val, zpow_one]

/-- **PACKAGE J.**  The full-turn shift of the parameter multiplies the reference
implementer by `(-1)^k`, written with real coefficients. -/
theorem Un_shift_val (n : Vec3) (θ : ℝ) (k : ℤ) :
    Un n (θ + 2 * Real.pi * k) = ((-1 : ℝ) ^ k) • Un n θ := by
  refine Int.induction_on k ?_ ?_ ?_
  · norm_num
  · intro m hm
    have hstep : Un n (θ + 2 * Real.pi * (((m : ℤ) + 1 : ℤ) : ℝ))
        = -(Un n (θ + 2 * Real.pi * ((m : ℤ) : ℝ))) := by
      rw [show θ + 2 * Real.pi * (((m : ℤ) + 1 : ℤ) : ℝ)
          = (θ + 2 * Real.pi * ((m : ℤ) : ℝ)) + 2 * Real.pi by push_cast; ring]
      exact NullSectorTask21.Un_add_two_pi n _
    rw [hstep, hm, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_one]
    module
  · intro m hm
    have hx : Un n (θ + 2 * Real.pi * ((-(m : ℤ) : ℤ) : ℝ))
        = -(Un n (θ + 2 * Real.pi * ((-(m : ℤ) - 1 : ℤ) : ℝ))) := by
      have h := NullSectorTask21.Un_add_two_pi n (θ + 2 * Real.pi * ((-(m : ℤ) - 1 : ℤ) : ℝ))
      rw [show θ + 2 * Real.pi * ((-(m : ℤ) - 1 : ℤ) : ℝ) + 2 * Real.pi
          = θ + 2 * Real.pi * ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring] at h
      exact h
    have hstep : Un n (θ + 2 * Real.pi * ((-(m : ℤ) - 1 : ℤ) : ℝ))
        = -(Un n (θ + 2 * Real.pi * ((-(m : ℤ) : ℤ) : ℝ))) := by
      rw [hx]; module
    have hval : ((-1 : ℝ) ^ ((-(m : ℤ) - 1 : ℤ))) = -((-1 : ℝ) ^ ((-(m : ℤ) : ℤ))) := by
      rw [show ((-(m : ℤ) - 1 : ℤ)) = (-(m : ℤ)) + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      norm_num
    rw [hstep, hm, hval]
    module

/-- **PACKAGE J (items 76, 77), principal.**  Under a full-turn shift of the parameter the
core representative is multiplied exactly by the parity sign of the number of turns. -/
theorem Un_shift (n : Vec3) (θ : ℝ) (k : ℤ) :
    Un n (θ + 2 * Real.pi * k) = ((parityMap k : Sgn) : ℝ) • Un n θ := by
  rw [parityMap_val]
  exact Un_shift_val n θ k

/-- **PACKAGE J.**  The same statement inside the frozen core carrier: the full-turn shift
acts by the parity sign. -/
theorem sact_parity_Un {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (k : ℤ) :
    (⟨Un n (θ + 2 * Real.pi * k), Un_mem_Lift hn _⟩ : LiftT)
      = sact (parityMap k) ⟨Un n θ, Un_mem_Lift hn θ⟩ :=
  Subtype.ext (Un_shift n θ k)

/-! ## What the integer labels do *not* determine (items 78–80) -/

/-- **PACKAGE J (item 78).**  The integer label is completely invisible to the certified core
projection: two old locally exact families with different labels have the same visible
image at every axis and parameter. -/
theorem label_invisible_to_core (k k' : ℤ) {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    proj (locFam k n θ) = proj (locFam k' n θ) := by
  rw [proj_locFam k hn, proj_locFam k' hn]

/-- **PACKAGE J.**  Full-turn evaluation of an *integer* central label difference is `+1` for
every integer: on the central side the induced map `ℤ → {+1,-1}` is trivial, not parity. -/
theorem full_turn_integer_label_trivial (m : ℤ) :
    labelBridge (m : ℝ) (2 * Real.pi) = w1 := by
  rw [labelBridge_eq]
  have hang : (m : ℝ) * (2 * Real.pi) = 0 + (m : ℝ) * (2 * Real.pi) := by ring
  rw [hang, Real.cos_add_int_mul_two_pi 0 m, Real.sin_add_int_mul_two_pi 0 m, Real.cos_zero,
    Real.sin_zero, zc_one_zero]

/-- **PACKAGE J (item 79).**  Explicit distinct integer data producing the same kernel sign:
the parity map identifies all integers of equal parity. -/
theorem distinct_labels_same_sign :
    (0 : ℤ) ≠ 2 ∧ parityMap 0 = parityMap 2 ∧ (1 : ℤ) ≠ 3 ∧ parityMap 1 = parityMap 3 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_⟩
  · rw [(parityMap_eq_one_iff 0).2 (by decide), (parityMap_eq_one_iff 2).2 (by decide)]
  · refine Subtype.ext ?_
    rw [parityMap_val, parityMap_val]
    norm_num

/-- **PACKAGE J (item 80).**  The two-valued data are *not* sufficient for the extended
structure: two distinct old labels have the same full-turn value while their central factors
differ at some parameter.  This is the inherited Task-20 statement, recorded here as the
exact boundary of what the overlap signs can reconstruct. -/
theorem sign_data_insufficient_for_extended :
    ∃ b b' : ℝ, b ∈ HalfOddSet ∧ b' ∈ HalfOddSet ∧ (∃ k : ℤ, b' = b + 2 * (k : ℝ)) ∧
      (∃ θ : ℝ, labelBridge b θ ≠ labelBridge b' θ) ∧
      labelBridge b (2 * Real.pi) = labelBridge b' (2 * Real.pi) :=
  reduction_loses_information

end NullSectorTask23
