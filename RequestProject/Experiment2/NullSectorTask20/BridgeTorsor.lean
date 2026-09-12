import RequestProject.Experiment2.NullSectorTask20.VisibleQuotient

/-!
# Task 20, Layer 4 (Packages D and E): relative factors and the affine label structure

Phase A only.

**Package D.**  The inherited primitive bridge is identified, intrinsically, as *the unique
relative factor between two internal lifts of the same visible datum*: for two elements of
the full internal carrier with equal projection there is exactly one invertible central
element converting one into the other, and for two elements of the internal **core** carrier
the relative factor is exactly a sign.  Both statements are pure internal algebra: no
continuity and no exactness is used.  (By contrast, the inherited exact normal form
`c n θ = zexp (primRateA c n) (primRateB c n) θ` is a theorem whose hypothesis
`IsPrimitiveBridge` explicitly contains joint continuity.)

**Package E.**  The set of locally exact directional rates is frozen as a subset of the
reals; the integer differences act on it; the action is proved free and transitive and the
set is proved to have no distinguished element (it is an affine `ℤ`-object, not a group);
the set of differences is proved to be exactly `ℤ`; and the loss of information under
reduction modulo a proper subgroup is exhibited by an explicit witness, together with the
exact statement of what such a reduction still preserves.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## Package D — the relative factor between internal lifts -/

/-- **PACKAGE D, principal (items 37, 38).**  Two elements of the full internal carrier with
the same visible projection differ by exactly one invertible central factor.  Existence and
uniqueness; no continuity, no exactness. -/
theorem relative_factor_existsUnique {u u' : W} (hu : u ∈ LiftZ) (hu' : u' ∈ LiftZ)
    (h : proj u = proj u') : ∃! z : W, z ∈ CUnit ∧ u = z ⋆ u' := by
  obtain ⟨v, hv, hv1, hv2⟩ := LiftZ_inv_mem hu'
  refine ⟨u ⋆ v, ⟨?_, ?_⟩, ?_⟩
  · have hmem : u ⋆ v ∈ LiftZ := LiftZ_mul_mem hu hv
    have hid : proj (u ⋆ v) = LinearMap.id := by
      rw [proj_mul (isInvertible_of_mem_LiftZ hu) (isInvertible_of_mem_LiftZ hv), h,
        ← proj_mul (isInvertible_of_mem_LiftZ hu') (isInvertible_of_mem_LiftZ hv), hv1, proj_w1]
    have : u ⋆ v ∈ {w : W | w ∈ LiftZ ∧ proj w = LinearMap.id} := ⟨hmem, hid⟩
    rwa [kernel_full] at this
  · rw [mul_assoc_W, hv2, mul_one_W]
  · rintro z ⟨-, hz⟩
    calc z = z ⋆ w1 := (mul_one_W z).symm
      _ = z ⋆ (u' ⋆ v) := by rw [hv1]
      _ = (z ⋆ u') ⋆ v := (mul_assoc_W z u' v).symm
      _ = u ⋆ v := by rw [← hz]

/-- **PACKAGE D (item 37, core version).**  Between two elements of the internal core carrier
with the same visible projection the relative factor is exactly a sign. -/
theorem relative_factor_core {u u' : W} (hu : u ∈ Lift) (hu' : u' ∈ Lift)
    (h : proj u = proj u') : u = u' ∨ u = -u' := by
  obtain ⟨v, hv, hv1, hv2⟩ := Lift_inv_mem hu'
  have hmem : u ⋆ v ∈ Lift := Lift_mul_mem hu hv
  have hid : proj (u ⋆ v) = LinearMap.id := by
    rw [proj_mul (isInvertible_of_mem_Lift hu) (isInvertible_of_mem_Lift hv), h,
      ← proj_mul (isInvertible_of_mem_Lift hu') (isInvertible_of_mem_Lift hv), hv1, proj_w1]
  have hker : u ⋆ v ∈ ({w1, -w1} : Set W) := by
    rw [← kernel_core]; exact ⟨hmem, hid⟩
  have hback : (u ⋆ v) ⋆ u' = u := by rw [mul_assoc_W, hv2, mul_one_W]
  rcases hker with hcase | hcase
  · left; rw [← hback, hcase, one_mul_W]
  · right; rw [← hback, hcase, neg_mul_W, one_mul_W]

/-! ## Package E — the local exact rate set -/

/-- **NEUTRAL DEFINITION (item 44).**  The set of allowed locally exact directional rates,
written without any reference to the notation in which it first appeared. -/
def HalfOddSet : Set ℝ := {x : ℝ | IsHalfOdd x}

theorem mem_halfOddSet {x : ℝ} : x ∈ HalfOddSet ↔ ∃ k : ℤ, x = (k : ℝ) + 1 / 2 := Iff.rfl

theorem zero_notMem_halfOddSet : (0 : ℝ) ∉ HalfOddSet := by
  rintro ⟨k, hk⟩
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-- **PACKAGE E (item 45).**  The integer differences act on the local exact rate set. -/
theorem halfOddSet_add_int {x : ℝ} (hx : x ∈ HalfOddSet) (k : ℤ) : x + k ∈ HalfOddSet := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨m + k, by push_cast; linarith⟩

theorem halfOddSet_action_zero (x : ℝ) : x + ((0 : ℤ) : ℝ) = x := by norm_num

theorem halfOddSet_action_add (x : ℝ) (k l : ℤ) : (x + (k : ℝ)) + (l : ℝ) = x + ((k + l : ℤ) : ℝ) := by
  push_cast; ring

/-- **PACKAGE E (item 46).**  The action is free. -/
theorem halfOddSet_action_free {x : ℝ} {k : ℤ} (h : x + (k : ℝ) = x) : k = 0 := by
  have : (k : ℝ) = 0 := by linarith
  exact_mod_cast this

/-- **PACKAGE E (item 47).**  The action is transitive, with a unique translating integer. -/
theorem halfOddSet_action_transitive {x y : ℝ} (hx : x ∈ HalfOddSet) (hy : y ∈ HalfOddSet) :
    ∃! k : ℤ, x + (k : ℝ) = y := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨p, hp⟩ := hy
  refine ⟨p - m, by push_cast; linarith, ?_⟩
  intro l hl
  have : ((l : ℝ)) = ((p - m : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- **PACKAGE E (items 48, 49), principal.**  The local exact rate set is a nonempty free and
transitive `ℤ`-object with **no distinguished element**: it does not contain the neutral
element of the acting group's canonical model, every element can be moved to every other by
an equivariant translation, and no element is fixed by a nonzero translation. -/
theorem halfOddSet_torsor :
    (∃ x : ℝ, x ∈ HalfOddSet) ∧
      (0 : ℝ) ∉ HalfOddSet ∧
      (∀ x ∈ HalfOddSet, ∀ k : ℤ, x + (k : ℝ) ∈ HalfOddSet) ∧
      (∀ x ∈ HalfOddSet, ∀ k : ℤ, x + (k : ℝ) = x → k = 0) ∧
      (∀ x ∈ HalfOddSet, ∀ y ∈ HalfOddSet, ∃! k : ℤ, x + (k : ℝ) = y) :=
  ⟨⟨1 / 2, ⟨0, by norm_num⟩⟩, zero_notMem_halfOddSet,
    fun _ hx k => halfOddSet_add_int hx k, fun _ _ _ h => halfOddSet_action_free h,
    fun _ hx _ hy => halfOddSet_action_transitive hx hy⟩

/-- **PACKAGE E (item 43), principal.**  The relative data between two allowed rates form
exactly the integers — a group — although the rate set itself carries no origin.  This is the
exact sense in which relative factors obey a closed law independent of absolute choices. -/
theorem halfOddSet_differences :
    {d : ℝ | ∃ x ∈ HalfOddSet, ∃ y ∈ HalfOddSet, d = y - x} = {d : ℝ | ∃ k : ℤ, d = (k : ℝ)} := by
  ext d
  constructor
  · rintro ⟨x, ⟨m, hm⟩, y, ⟨p, hp⟩, rfl⟩
    exact ⟨p - m, by push_cast; linarith⟩
  · rintro ⟨k, rfl⟩
    exact ⟨1 / 2, ⟨0, by norm_num⟩, (k : ℝ) + 1 / 2, ⟨k, rfl⟩, by ring⟩

/-! ## Package E — the labelled central bridges -/

/-- **NEUTRAL DEFINITION.**  The central one-parameter factor carrying a directional label. -/
noncomputable def labelBridge (b : ℝ) (θ : ℝ) : W := zexp 0 b θ

theorem labelBridge_eq (b θ : ℝ) : labelBridge b θ = zc (Real.cos (b * θ)) (Real.sin (b * θ)) := by
  simp [labelBridge, zexp]

/-- **DERIVED.**  Labels add under the inherited product. -/
theorem labelBridge_mul (b b' θ : ℝ) :
    labelBridge b θ ⋆ labelBridge b' θ = labelBridge (b + b') θ := by
  rw [labelBridge_eq, labelBridge_eq, labelBridge_eq, zc_mul_zc]
  rw [show (b + b') * θ = b * θ + b' * θ by ring, Real.cos_add, Real.sin_add]
  congr 1
  ring

/-- **PACKAGE E (item 50).**  The value after a full turn of the parameter is the same for
**every** allowed label: no reduction of the integer relative data can lose it. -/
theorem labelBridge_full_turn {b : ℝ} (hb : b ∈ HalfOddSet) :
    labelBridge b (2 * Real.pi) = -w1 := by
  obtain ⟨k, hk⟩ := hb
  rw [labelBridge_eq, hk]
  have hang : ((k : ℝ) + 1 / 2) * (2 * Real.pi) = Real.pi + (k : ℝ) * (2 * Real.pi) := by ring
  rw [hang, Real.cos_add_int_mul_two_pi Real.pi k, Real.sin_add_int_mul_two_pi Real.pi k,
    Real.cos_pi, Real.sin_pi, zc]
  module

/-- **PACKAGE E.**  Distinct labels give genuinely distinct central factors. -/
theorem labelBridge_injective {b b' : ℝ} (h : ∀ θ : ℝ, labelBridge b θ = labelBridge b' θ) :
    b = b' := by
  have hc : IsPrimitiveBridge (cexp 0 b) := cexp_isPrimitiveBridge 0 b
  have hrates := cexp_rates 0 b (n := e1) e1_isUnitAxis
  have heq : ∀ θ : ℝ, cexp 0 b e1 θ = zexp 0 b' θ := fun θ => h θ
  obtain ⟨-, hB⟩ := primitiveBridge_rates_unique hc e1_isUnitAxis (α := 0) (β := b') heq
  rw [hrates.2] at hB
  exact hB.symm

/-- **PACKAGE E (item 51), principal.**  Reduction of the integer relative data modulo a
proper subgroup loses information: an explicit pair of allowed labels differing by an even
integer, with genuinely different central factors, while the full-turn value — which such a
reduction is designed to keep — is the same for both. -/
theorem reduction_loses_information :
    ∃ b b' : ℝ, b ∈ HalfOddSet ∧ b' ∈ HalfOddSet ∧ (∃ k : ℤ, b' = b + 2 * (k : ℝ)) ∧
      (∃ θ : ℝ, labelBridge b θ ≠ labelBridge b' θ) ∧
      labelBridge b (2 * Real.pi) = labelBridge b' (2 * Real.pi) := by
  refine ⟨1 / 2, 5 / 2, ⟨0, by norm_num⟩, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩, ?_, ?_⟩
  · refine ⟨Real.pi / 2, ?_⟩
    rw [labelBridge_eq, labelBridge_eq]
    intro hcon
    have h0 := congrFun hcon 0
    simp only [zc_coord_0] at h0
    have e1' : (1 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 := by ring
    have e2' : (5 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 + Real.pi := by ring
    rw [e1', e2', Real.cos_add_pi] at h0
    have hpos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [hpos] at h0
    have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.2 (by norm_num)
    linarith
  · rw [labelBridge_full_turn ⟨0, by norm_num⟩, labelBridge_full_turn ⟨2, by norm_num⟩]

end NullSectorTask20
