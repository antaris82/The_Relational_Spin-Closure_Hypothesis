import RequestProject.Experiment2.NullSectorTask14.SecondAxisAutomorphism

/-!
# Task 14, Layer 3 (§12–§14): the independent second-axis internal implementation

**INDEPENDENT SECOND-AXIS DERIVATION.**  We look for one-parameter families `V : ℝ → W`
implementing the independently reconstructed second-axis automorphism family by
conjugation.  No subspace is prescribed in advance and no half-angle formula and no
square-minus-one generator is assumed: both are *derived*.

Order of this module:

1. the unrestricted implementation problem `IsBLift`;
2. the relative theorem (§14): two implementers of the same automorphism differ by a
   factor which is forced to lie in the **exact center** — the Task-11 theorem
   `center_eq_Z` is used here explicitly and is the only external input;
3. the internal two-plane that the search actually forces, together with the derived
   relation `Q ⋆ Q = -1`;
4. the derived half-angle constraint;
5. only then the explicit reference implementer and its verification;
6. the derived infinitesimal generator.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §12 — the unrestricted implementation problem -/

/-- **NEUTRAL DEFINITION (§12).**  A one-parameter family of carrier elements implementing
the independently reconstructed second-axis automorphism family by conjugation.  No
membership in any subspace, no normalization, no continuity. -/
structure IsBLift (V : ℝ → W) : Prop where
  /-- Normalization at the zero parameter (not a norm condition). -/
  unit : V 0 = w1
  /-- One-parameter composition law. -/
  group : ∀ φ χ : ℝ, V (φ + χ) = V φ ⋆ V χ
  /-- The conjugation action is the second-axis automorphism family. -/
  conj : ∀ (φ : ℝ) (x : W), (V φ ⋆ x) ⋆ V (-φ) = PhiB φ x

namespace IsBLift

variable {V : ℝ → W} (hV : IsBLift V)
include hV

theorem mul_neg (φ : ℝ) : V φ ⋆ V (-φ) = w1 := by
  have h := hV.group φ (-φ)
  rw [add_neg_cancel, hV.unit] at h
  exact h.symm

theorem neg_mul (φ : ℝ) : V (-φ) ⋆ V φ = w1 := by
  have h := hV.group (-φ) φ
  rw [neg_add_cancel, hV.unit] at h
  exact h.symm

theorem ne_zero (φ : ℝ) : V φ ≠ 0 := by
  intro hzero
  have h := hV.mul_neg φ
  rw [hzero, zero_mul_W] at h
  have h0 : (0 : W) 0 = (w1 : W) 0 := by rw [h]
  simp [w1] at h0

end IsBLift

/-! ## §14 — the relative theorem: the residual factor is exactly central -/

/-- **PRINCIPAL THEOREM (§14): `second_axis_relative_central`.**  Any two implementations
of the *same* second-axis automorphism family differ, at every parameter value, by a
factor lying in the **exact center** `Z`.

*Dependency (stated explicitly, §14).*  The final step uses the Task-11 exact-center
theorem `center_eq_Z`; the rest is derived from the two implementation properties. -/
theorem bLift_relative_central {V V' : ℝ → W} (hV : IsBLift V) (hV' : IsBLift V')
    (φ : ℝ) : V φ ⋆ V' (-φ) ∈ Z := by
  refine mem_Z_of_comm_all (fun x => ?_)
  have key : ∀ y : W, V' (-φ) ⋆ y = PhiB (-φ) y ⋆ V' (-φ) := by
    intro y
    have h := hV'.conj (-φ) y
    rw [neg_neg] at h
    calc V' (-φ) ⋆ y = ((V' (-φ) ⋆ y) ⋆ V' φ) ⋆ V' (-φ) := by
          rw [mul_assoc_W (V' (-φ) ⋆ y) (V' φ) (V' (-φ)), hV'.mul_neg φ, mul_one_W]
      _ = PhiB (-φ) y ⋆ V' (-φ) := by rw [h]
  have key2 : ∀ y : W, V φ ⋆ PhiB (-φ) y = PhiB φ (PhiB (-φ) y) ⋆ V φ := by
    intro y
    have h := hV.conj φ (PhiB (-φ) y)
    calc V φ ⋆ PhiB (-φ) y
        = ((V φ ⋆ PhiB (-φ) y) ⋆ V (-φ)) ⋆ V φ := by
          rw [mul_assoc_W (V φ ⋆ PhiB (-φ) y) (V (-φ)) (V φ), hV.neg_mul φ, mul_one_W]
      _ = PhiB φ (PhiB (-φ) y) ⋆ V φ := by rw [h]
  have hcomp : ∀ y : W, PhiB φ (PhiB (-φ) y) = y := by
    intro y
    have := PhiB_add_apply φ (-φ) y
    rw [add_neg_cancel, PhiB_zero] at this
    exact this.symm
  calc (V φ ⋆ V' (-φ)) ⋆ x = V φ ⋆ (V' (-φ) ⋆ x) := mul_assoc_W _ _ _
    _ = V φ ⋆ (PhiB (-φ) x ⋆ V' (-φ)) := by rw [key x]
    _ = (V φ ⋆ PhiB (-φ) x) ⋆ V' (-φ) := (mul_assoc_W _ _ _).symm
    _ = (PhiB φ (PhiB (-φ) x) ⋆ V φ) ⋆ V' (-φ) := by rw [key2 x]
    _ = (x ⋆ V φ) ⋆ V' (-φ) := by rw [hcomp x]
    _ = x ⋆ (V φ ⋆ V' (-φ)) := mul_assoc_W _ _ _

/-- **PRINCIPAL THEOREM (§14), explicit form.**  Two implementers differ by a central
factor: `V φ = z ⋆ V' φ` with `z ∈ Z`. -/
theorem bLift_relative_factor {V V' : ℝ → W} (hV : IsBLift V) (hV' : IsBLift V') (φ : ℝ) :
    ∃ z ∈ Z, V φ = z ⋆ V' φ := by
  refine ⟨V φ ⋆ V' (-φ), bLift_relative_central hV hV' φ, ?_⟩
  rw [mul_assoc_W, hV'.neg_mul, mul_one_W]

/-! ## §12 — the internal two-plane that the search forces -/

/-- **DERIVED (§13), not assumed.**  The unique noncentral basis direction left fixed by
the second-axis automorphism family squares to minus the unit. -/
theorem wQ_sq : wQ ⋆ wQ = -w1 := wit8_wQ_wQ

/-- **NEUTRAL DEFINITION.**  A general element of the internal two-plane spanned by the
unit and the fixed noncentral direction. -/
noncomputable def kB (a b : ℝ) : W := a • w1 + b • wQ

@[simp] theorem kB_coord_0 (a b : ℝ) : kB a b 0 = a := by simp [kB, w1, wQ]
@[simp] theorem kB_coord_5 (a b : ℝ) : kB a b 5 = b := by simp [kB, w1, wQ]

theorem kB_mul_kB (a b c d : ℝ) : kB a b ⋆ kB c d = kB (a * c - b * d) (a * d + b * c) := by
  simp only [kB, add_mul_W, mul_add_W, smul_mul_W, mul_smul_W, one_mul_W, mul_one_W, wQ_sq]
  module

theorem kB_one : kB 1 0 = w1 := by simp [kB]

theorem kB_eq_zero_iff (a b : ℝ) : kB a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hk
    exact ⟨by simpa using congrFun hk 0, by simpa using congrFun hk 5⟩
  · rintro ⟨rfl, rfl⟩
    funext i; fin_cases i <;> simp [kB, w1, wQ]

/-- **NEUTRAL DEFINITION.**  The internal two-plane, described by its coordinates. -/
def KBplane : Submodule ℝ W where
  carrier := {x | x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 6 = 0 ∧ x 7 = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3, h4, h6, h7⟩ ⟨k1, k2, k3, k4, k6, k7⟩
    exact ⟨by simp [h1, k1], by simp [h2, k2], by simp [h3, k3], by simp [h4, k4],
      by simp [h6, k6], by simp [h7, k7]⟩
  zero_mem' := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3, h4, h6, h7⟩
    exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h6], by simp [h7]⟩

theorem mem_KBplane_iff (x : W) : x ∈ KBplane ↔ ∃ a b : ℝ, x = kB a b := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h6, h7⟩
    refine ⟨x 0, x 5, ?_⟩
    funext i
    fin_cases i <;> simp [kB, w1, wQ, h1, h2, h3, h4, h6, h7]
  · rintro ⟨a, b, rfl⟩
    exact ⟨by simp [kB, w1, wQ], by simp [kB, w1, wQ], by simp [kB, w1, wQ],
      by simp [kB, w1, wQ], by simp [kB, w1, wQ], by simp [kB, w1, wQ]⟩

theorem KBplane_mul_closed {x y : W} (hx : x ∈ KBplane) (hy : y ∈ KBplane) :
    x ⋆ y ∈ KBplane := by
  obtain ⟨a, b, rfl⟩ := (mem_KBplane_iff x).1 hx
  obtain ⟨c, d, rfl⟩ := (mem_KBplane_iff y).1 hy
  rw [kB_mul_kB]
  exact (mem_KBplane_iff _).2 ⟨_, _, rfl⟩

theorem finrank_KBplane : Module.finrank ℝ (KBplane : Submodule ℝ W) = 2 := by
  have hspan : KBplane = Submodule.span ℝ (Set.range ![w1, wQ]) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨a, b, rfl⟩ := (mem_KBplane_iff x).1 hx
      have : kB a b = a • w1 + b • wQ := rfl
      rw [this]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span ⟨0, by simp⟩
      · exact Submodule.subset_span ⟨1, by simp⟩
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact (mem_KBplane_iff _).2 ⟨1, 0, by simp [kB]⟩
      · exact (mem_KBplane_iff _).2 ⟨0, 1, by simp [kB]⟩
  have hli : LinearIndependent ℝ ![w1, wQ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    exact (kB_eq_zero_iff s t).1 hst
  rw [hspan, finrank_span_eq_card hli]
  simp

/-! ## §13 — the half-angle is derived, not assumed -/

/-- **DERIVED (§13).**  The exact conjugation of the first transverse direction by a
general element of the internal two-plane. -/
theorem kB_conj_wA (a b : ℝ) :
    (kB a b ⋆ wA) ⋆ kB a (-b) = (a ^ 2 - b ^ 2) • wA + (-(2 * a * b)) • wC := by
  funext i; fin_cases i <;> simp [kB, wA, wC, w1, wQ, wit8MulFun] <;> ring

/-- **DERIVED (§13): `second_axis_half_angle_forced`.**  Suppose an element of the internal
two-plane conjugates the first transverse direction exactly as the second-axis
automorphism does.  Then its two coefficients are forced to satisfy the *half-angle*
relations; no half-angle formula was assumed. -/
theorem second_axis_half_angle_forced {a b φ : ℝ}
    (hconj : (kB a b ⋆ wA) ⋆ kB a (-b) = PhiB φ wA) :
    a ^ 2 - b ^ 2 = Real.cos φ ∧ 2 * a * b = Real.sin φ := by
  rw [kB_conj_wA, PhiB_wA] at hconj
  have h1 := congrFun hconj 1
  have h3 := congrFun hconj 3
  simp [wA, wC] at h1 h3
  exact ⟨h1, by linarith⟩

/-! ## The reference implementer, derived from the half-angle constraint -/

/-- **DERIVED REFERENCE IMPLEMENTER (§13).**  The solution of the half-angle constraint on
the unit circle of the internal two-plane. -/
noncomputable def UBref (φ : ℝ) : W := kB (Real.cos (φ / 2)) (Real.sin (φ / 2))

theorem UBref_apply (φ : ℝ) :
    UBref φ = Real.cos (φ / 2) • w1 + Real.sin (φ / 2) • wQ := rfl

@[simp] theorem UBref_zero : UBref 0 = w1 := by simp [UBref, kB]

theorem UBref_neg (φ : ℝ) : UBref (-φ) = kB (Real.cos (φ / 2)) (-Real.sin (φ / 2)) := by
  rw [UBref, show -φ / 2 = -(φ / 2) by ring, Real.cos_neg, Real.sin_neg]

theorem UBref_group (φ χ : ℝ) : UBref (φ + χ) = UBref φ ⋆ UBref χ := by
  rw [UBref, UBref, UBref, kB_mul_kB, show (φ + χ) / 2 = φ / 2 + χ / 2 by ring,
    Real.cos_add, Real.sin_add]
  congr 1
  ring

theorem UBref_mul_neg (φ : ℝ) : UBref φ ⋆ UBref (-φ) = w1 := by
  rw [← UBref_group, add_neg_cancel, UBref_zero]

theorem UBref_mem_KBplane (φ : ℝ) : UBref φ ∈ KBplane :=
  (mem_KBplane_iff _).2 ⟨_, _, rfl⟩

/-- **PRINCIPAL THEOREM (§13): `second_axis_reference_implementation`.**  The derived
reference family implements the independently reconstructed second-axis automorphism
family by conjugation. -/
theorem UBref_conj (φ : ℝ) (x : W) : (UBref φ ⋆ x) ⋆ UBref (-φ) = PhiB φ x := by
  have hh : φ = 2 * (φ / 2) := by ring
  have hcc : Real.cos φ = Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 := by
    conv_lhs => rw [hh]
    rw [Real.cos_two_mul']
  have hss : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    conv_lhs => rw [hh]
    rw [Real.sin_two_mul]
  have hpy := Real.sin_sq_add_cos_sq (φ / 2)
  have hneg : UBref (-φ) = Real.cos (φ / 2) • w1 + (-Real.sin (φ / 2)) • wQ := by
    rw [UBref_neg, kB]
  obtain ⟨u, hu⟩ : ∃ u, Real.cos (φ / 2) = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, Real.sin (φ / 2) = v := ⟨_, rfl⟩
  rw [hu, hv] at hcc hss hpy hneg
  rw [UBref_apply, hu, hv, hneg]
  have hv2 : v ^ 2 = 1 - u ^ 2 := by linarith
  funext i
  fin_cases i <;>
    simp [w1, wQ, wit8MulFun, hcc, hss] <;> ring_nf <;> (try simp only [hv2]) <;> (try ring)

/-- **PRINCIPAL THEOREM (§12/§13): `second_axis_implementation_exists`. -/
theorem UBref_isBLift : IsBLift UBref where
  unit := UBref_zero
  group := UBref_group
  conj := UBref_conj

/-- **PRINCIPAL THEOREM (§12): `second_axis_minimal_implementer_plane`.**  The smallest
product-closed real subspace containing the whole derived reference family is exactly the
internal two-plane spanned by the unit and the fixed noncentral direction; its real
dimension is two. -/
theorem second_axis_forced_plane :
    (∀ φ, UBref φ ∈ KBplane) ∧
    (∀ x ∈ KBplane, ∀ y ∈ KBplane, x ⋆ y ∈ KBplane) ∧
    Module.finrank ℝ (KBplane : Submodule ℝ W) = 2 ∧
    (∀ M : Submodule ℝ W, (∀ φ, UBref φ ∈ M) → KBplane ≤ M) := by
  refine ⟨UBref_mem_KBplane, fun _ hx _ hy => KBplane_mul_closed hx hy, finrank_KBplane,
    fun M hM => ?_⟩
  have h1 : w1 ∈ M := by simpa using hM 0
  have h2 : wQ ∈ M := by
    have hpi := hM Real.pi
    have : UBref Real.pi = wQ := by
      rw [UBref, show Real.pi / 2 = Real.pi / 2 from rfl]
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
      funext i; fin_cases i <;> simp [kB, w1, wQ]
    rwa [this] at hpi
  intro x hx
  obtain ⟨a, b, rfl⟩ := (mem_KBplane_iff x).1 hx
  have : kB a b = a • w1 + b • wQ := rfl
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

/-! ## §13 — the derived infinitesimal generator -/

/-- **DERIVED (§13).**  The infinitesimal generator of the derived reference family. -/
noncomputable def GB : W := (2⁻¹ : ℝ) • wQ

theorem hasDerivAt_cos_half (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (t / 2)) (-Real.sin (θ / 2) * (1 / 2)) θ := by
  have h : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id θ).div_const 2
  simpa using h.cos

theorem hasDerivAt_sin_half (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (Real.cos (θ / 2) * (1 / 2)) θ := by
  have h : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id θ).div_const 2
  simpa using h.sin

/-- **DERIVED (§13): `second_axis_generator`.**  `GB` is the derivative of the derived
reference family at the zero parameter. -/
theorem hasDerivAt_UBref_zero : HasDerivAt UBref GB 0 := by
  have hfun : UBref = fun φ : ℝ => Real.cos (φ / 2) • w1 + Real.sin (φ / 2) • wQ := by
    funext φ; rw [UBref_apply]
  rw [hfun]
  have hd :=
    ((hasDerivAt_cos_half 0).smul_const w1).add ((hasDerivAt_sin_half 0).smul_const wQ)
  convert hd using 1
  rw [GB]
  norm_num

/-- **DERIVED (§13).**  The derived generator squares to minus a quarter of the unit; in
particular the *direction* of the generator squares to `-1`.  Neither was assumed. -/
theorem GB_sq : GB ⋆ GB = (-(4⁻¹ : ℝ)) • w1 := by
  rw [GB, smul_mul_W, mul_smul_W, wQ_sq]
  module

end NullSectorTask14
