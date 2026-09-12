import RequestProject.Experiment2.NullSectorTask21.NormalizedCentralCarrier

/-!
# Task 21, Package F: the two distinct two-valued structures

**IDENTIFICATION / COMPARISON MODULE** (all statements are intrinsic; the module is placed
here because it is read together with Packages D and E).

Task 20 exposed two different two-valued phenomena, which must not be conflated:

* the **core-kernel sign** `g ↦ -g` inside the internal core carrier;
* the **direction reversal** `n ↦ -n` on the carrier of unit directions.

This module proves the exact action of each, the exact axis-angle relation between `(n,θ)`
and `(-n,-θ)`, and the exact way the two are coupled through the parameterization — and it
proves that they are *not* the same two-valued structure.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-! ## The core-kernel sign -/

theorem invW_neg {u : W} (hu : IsInvertible u) : invW (-u) = -invW u := by
  obtain ⟨h1, h2⟩ := invW_spec hu
  refine invW_eq ?_ ?_
  · rw [neg_mul_W, mul_neg_W, neg_neg, h1]
  · rw [neg_mul_W, mul_neg_W, neg_neg, h2]

/-- **PACKAGE F (item 58).**  The exact action of the core sign on the visible projection:
it is invisible. -/
theorem proj_neg {u : W} (hu : IsInvertible u) : proj (-u) = proj u := by
  refine LinearMap.ext fun x => ?_
  simp only [proj_apply, invW_neg hu, neg_mul_W, mul_neg_W, neg_neg]

/-- **PACKAGE F.**  The packaged form: multiplying by the sign element does not change the
visible transformation. -/
theorem projCore_sign (g : LiftG) : projCore (lNegOne * g) = projCore g := by
  refine Subtype.ext (Units.ext ?_)
  show proj ((WG.negOne * (g : WG)).val) = proj ((g : WG)).val
  have hval : (WG.negOne * (g : WG)).val = -((g : WG)).val := by
    show (-w1) ⋆ ((g : WG)).val = -((g : WG)).val
    rw [neg_mul_W, one_mul_W]
  rw [hval, proj_neg (isInvertible_of_mem_Lift g.2)]

theorem zero_notMem_Lift : (0 : W) ∉ Lift := by
  rintro ⟨a, v, ha, hval⟩
  have h0 : a = 0 := by have := congrFun hval 0; simpa [w1] using this.symm
  have h4 : v.2.2 = 0 := by have := congrFun hval 4; simpa [w1] using this.symm
  have h5 : v.2.1 = 0 := by have := congrFun hval 5; simpa [w1] using this.symm
  have h6 : v.1 = 0 := by have := congrFun hval 6; simpa [w1] using this.symm
  rw [h0] at ha
  simp only [h3, dot3, h4, h5, h6] at ha
  norm_num at ha

/-- **PACKAGE F.**  The core sign is free: no core element equals its own negative. -/
theorem core_sign_free (g : LiftG) : lNegOne * g ≠ g := by
  intro h
  have hval : (-w1) ⋆ ((g : WG)).val = ((g : WG)).val :=
    congrArg (fun u : LiftG => (u : WG).val) h
  rw [neg_mul_W, one_mul_W] at hval
  have hzero : ((g : WG)).val = 0 := by
    have h2 : ((g : WG)).val + ((g : WG)).val = 0 := by
      rw [← neg_eq_iff_add_eq_zero]
      exact hval
    have := congrArg (fun x : W => (2 : ℝ)⁻¹ • x) h2
    simpa [smul_add, ← two_smul ℝ] using this
  exact zero_notMem_Lift (hzero ▸ g.2)

/-! ## The direction reversal -/

/-- **PACKAGE F (item 59).**  The exact axis-angle relation: reversing the direction and the
parameter simultaneously gives back exactly the same reference implementer. -/
theorem Un_neg_axis (n : Vec3) (θ : ℝ) : Un (-n) θ = Un n (-θ) := by
  rw [Un, NullSectorTask20.Jmap_neg, Un_neg]
  module

theorem Un_neg_axis_neg_param (n : Vec3) (θ : ℝ) : Un (-n) (-θ) = Un n θ := by
  rw [Un_neg_axis, neg_neg]

/-- **PACKAGE F.**  Consequently the reversed pair is visibly identical, with no core sign
involved. -/
theorem visRel_reversal (s : Sph) (θ : ℝ) : visRel (negSph s, -θ) (s, θ) := by
  show PhiGen (-(s : Vec3)) (-θ) = PhiGen (s : Vec3) θ
  refine LinearMap.ext fun x => ?_
  simp only [PhiGen_apply, Un_neg_axis, neg_neg]

/-- **PACKAGE F.**  The core sign is exactly a full-turn parameter shift. -/
theorem Un_add_two_pi (n : Vec3) (θ : ℝ) : Un n (θ + 2 * Real.pi) = -(Un n θ) := by
  have hc : Real.cos ((θ + 2 * Real.pi) / 2) = -Real.cos (θ / 2) := by
    rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.cos_add_pi]
  have hs : Real.sin ((θ + 2 * Real.pi) / 2) = -Real.sin (θ / 2) := by
    rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.sin_add_pi]
  rw [Un, Un, hc, hs]
  module

/-- **PACKAGE F (items 60–62).**  The two two-valued structures are *distinct*: the core sign
acts by a `2π` parameter shift and changes the internal element, while the direction reversal
acts by parameter reversal and changes no internal element.  Reversing the direction at the
*same* parameter is neither the identity nor the core sign. -/
theorem two_sign_structures_distinct :
    (∀ (n : Vec3) (θ : ℝ), Un n (θ + 2 * Real.pi) = -(Un n θ)) ∧
      (∀ (n : Vec3) (θ : ℝ), Un (-n) (-θ) = Un n θ) ∧
      (Un (-(1, 0, 0) : Vec3) (Real.pi / 2) ≠ Un ((1, 0, 0) : Vec3) (Real.pi / 2) ∧
        Un (-(1, 0, 0) : Vec3) (Real.pi / 2) ≠ -(Un ((1, 0, 0) : Vec3) (Real.pi / 2))) := by
  refine ⟨Un_add_two_pi, Un_neg_axis_neg_param, ?_, ?_⟩
  · have hs : Real.sin (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
      rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four]
    have hc : Real.cos (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
      rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four]
    have hpos : Real.sqrt 2 / 2 > 0 := by positivity
    intro h
    have h6 := congrFun h 6
    simp [Un, Jmap, w1, wR, wQ, wP, hs, hc] at h6
    linarith
  · have hs : Real.sin (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
      rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four]
    have hc : Real.cos (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
      rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four]
    have hpos : Real.sqrt 2 / 2 > 0 := by positivity
    intro h
    have h0 := congrFun h 0
    simp [Un, Jmap, w1, wR, wQ, wP, hs, hc] at h0
    linarith

/-- **PACKAGE F (item 63).**  The reversal quotient of the direction carrier is *not* the
two-element core kernel: it has at least three distinct elements.  Hence no identification of
the two quotients may be made without an explicit map. -/
theorem revQuot_not_two_element :
    ∃ a b c : RevQuot, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h1 : IsUnitAxis ((1, 0, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]
  have h2 : IsUnitAxis ((0, 1, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]
  have h3' : IsUnitAxis ((0, 0, 1) : Vec3) := by simp [IsUnitAxis, h3, dot3]
  refine ⟨revClass ⟨_, h1⟩, revClass ⟨_, h2⟩, revClass ⟨_, h3'⟩, ?_, ?_, ?_⟩ <;>
  · intro h
    rcases revClass_eq_iff.1 h with h' | h' <;>
      · have := congrArg Subtype.val h'
        simp [negSph, Prod.ext_iff] at this

end NullSectorTask21
