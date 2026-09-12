import RequestProject.Experiment2.NullSectorTask13.InfinitesimalRestriction

/-!
# Task 13, Layer 9: carrier equivalences against the axial structure (§29–§32)

Task 12 proved that any two minimal carriers are related by a bijective *restricted right
multiplication* `T_r(ψ) = ψ ⋆ r`.  The element `r` is **not** assumed to be globally
invertible anywhere below (§29): only the three defining properties of `CarrierEquiv` are
used, together with associativity.

## Results

* `carrier_equiv_intertwines_left` (§30, §31) — every such transformation commutes with
  left multiplication by *any* carrier element, hence with the reference lift and with
  every full lift; the Task-11 residual freedom is irrelevant to it;
* `carrier_equiv_preserves_plus_slice`, `carrier_equiv_preserves_minus_slice` (§32) —
  the axis-relative slices are matched exactly, proved from the defining `A`-eigenrelation
  and associativity, not from equal dimensions;
* `universal_axial_carrier_type` (§33) — the combined statement.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-! ## §30, §31 — intertwining of the axial actions -/

/-- **PRINCIPAL THEOREM (§30, §31): `carrier_equiv_intertwines_reference`,
`carrier_equiv_intertwines_full_lift`, `INTERTWINED`.**  A Task-12 carrier equivalence
commutes with left multiplication by every element of the algebra.  This is *derived from
associativity*, and therefore holds verbatim for the reference lift and for every full
lift with arbitrary residual `(α, β)` — the residual freedom does not affect carrier
equivalence at all. -/
theorem carrier_equiv_intertwines_left (r x ψ : W) : (x ⋆ ψ) ⋆ r = x ⋆ (ψ ⋆ r) :=
  mul_assoc_W x ψ r

theorem carrier_equiv_intertwines_reference (r ψ : W) (θ : ℝ) :
    (Uref θ ⋆ ψ) ⋆ r = Uref θ ⋆ (ψ ⋆ r) := mul_assoc_W _ _ _

theorem carrier_equiv_intertwines_fullLift {U : ℝ → W} (_hU : IsFullLift U) (r ψ : W)
    (θ : ℝ) : (U θ ⋆ ψ) ⋆ r = U θ ⋆ (ψ ⋆ r) := mul_assoc_W _ _ _

theorem carrier_equiv_intertwines_generator (r ψ : W) (α β : ℝ) :
    (Ggen α β ⋆ ψ) ⋆ r = Ggen α β ⋆ (ψ ⋆ r) := mul_assoc_W _ _ _

/-! ## §32 — the slices are matched exactly -/

/-- **DERIVED (§32).**  Right multiplication preserves each sector: this follows from the
defining `A`-eigenrelation and associativity alone. -/
theorem mul_right_mem_Hplus {ψ : W} (hψ : ψ ∈ Hplus) (r : W) : ψ ⋆ r ∈ Hplus := by
  rw [mem_Hplus_iff] at hψ ⊢
  rw [← mul_assoc_W, hψ]

theorem mul_right_mem_Hminus {ψ : W} (hψ : ψ ∈ Hminus) (r : W) : ψ ⋆ r ∈ Hminus := by
  rw [mem_Hminus_iff] at hψ ⊢
  rw [← mul_assoc_W, hψ, neg_mul_W]

/-- **PRINCIPAL THEOREM (§32): `carrier_equiv_preserves_plus_slice`,
`carrier_equiv_preserves_minus_slice`.**  Every Task-12 carrier equivalence carries the
plus slice of the source carrier *onto* the plus slice of the target carrier, and likewise
for the minus slices.  Equal dimensions are not used: surjectivity is obtained from the
inherited slice decomposition and the injectivity of the transformation. -/
theorem carrier_equiv_preserves_slices {L L' : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) (hL' : IsMinimalLeftCarrier L') {r : W}
    (hmap : ∀ ψ ∈ L, ψ ⋆ r ∈ L')
    (hinj : ∀ ψ ∈ L, ∀ φ ∈ L, ψ ⋆ r = φ ⋆ r → ψ = φ)
    (hsurj : ∀ φ ∈ L', ∃ ψ ∈ L, ψ ⋆ r = φ) :
    (∀ ψ ∈ Kplus L, ψ ⋆ r ∈ Kplus L') ∧
    (∀ ψ ∈ Kminus L, ψ ⋆ r ∈ Kminus L') ∧
    (∀ φ ∈ Kplus L', ∃ ψ ∈ Kplus L, ψ ⋆ r = φ) ∧
    (∀ φ ∈ Kminus L', ∃ ψ ∈ Kminus L, ψ ⋆ r = φ) := by
  have hP : ∀ ψ ∈ Kplus L, ψ ⋆ r ∈ Kplus L' := fun ψ hψ =>
    ⟨hmap ψ hψ.1, mul_right_mem_Hplus hψ.2 r⟩
  have hM : ∀ ψ ∈ Kminus L, ψ ⋆ r ∈ Kminus L' := fun ψ hψ =>
    ⟨hmap ψ hψ.1, mul_right_mem_Hminus hψ.2 r⟩
  refine ⟨hP, hM, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨ψ, hψL, hψr⟩ := hsurj φ hφ.1
    obtain ⟨hp, hm, hsum⟩ := slice_decomposition hL.1.1 hψL
    have hzero : (eminus ⋆ ψ) ⋆ r = 0 := by
      have hsplit : (eplus ⋆ ψ) ⋆ r + (eminus ⋆ ψ) ⋆ r = φ := by
        rw [← add_mul_W, ← hsum, hψr]
      have h1 : (eplus ⋆ ψ) ⋆ r ∈ Kplus L' := hP _ hp
      have h2 : (eminus ⋆ ψ) ⋆ r ∈ Kminus L' := hM _ hm
      have h3 : (eminus ⋆ ψ) ⋆ r ∈ Kplus L' := by
        have : (eminus ⋆ ψ) ⋆ r = φ - (eplus ⋆ ψ) ⋆ r := by rw [← hsplit]; abel
        rw [this]
        exact Submodule.sub_mem _ hφ h1
      have hbot := (carrier_slice_direct_sum hL').2
      have : (eminus ⋆ ψ) ⋆ r ∈ (⊥ : Submodule ℝ W) := by
        rw [← hbot]; exact ⟨h3, h2⟩
      simpa using this
    have hzero' : eminus ⋆ ψ = 0 := by
      have h0 : (0 : W) ⋆ r = 0 := zero_mul_W r
      exact hinj _ hm.1 0 (Submodule.zero_mem _) (by rw [hzero, h0])
    refine ⟨eplus ⋆ ψ, hp, ?_⟩
    have hψeq : ψ = eplus ⋆ ψ := by
      conv_lhs => rw [hsum]
      rw [hzero', add_zero]
    rw [← hψeq, hψr]
  · intro φ hφ
    obtain ⟨ψ, hψL, hψr⟩ := hsurj φ hφ.1
    obtain ⟨hp, hm, hsum⟩ := slice_decomposition hL.1.1 hψL
    have hzero : (eplus ⋆ ψ) ⋆ r = 0 := by
      have hsplit : (eplus ⋆ ψ) ⋆ r + (eminus ⋆ ψ) ⋆ r = φ := by
        rw [← add_mul_W, ← hsum, hψr]
      have h1 : (eplus ⋆ ψ) ⋆ r ∈ Kplus L' := hP _ hp
      have h2 : (eminus ⋆ ψ) ⋆ r ∈ Kminus L' := hM _ hm
      have h3 : (eplus ⋆ ψ) ⋆ r ∈ Kminus L' := by
        have : (eplus ⋆ ψ) ⋆ r = φ - (eminus ⋆ ψ) ⋆ r := by rw [← hsplit]; abel
        rw [this]
        exact Submodule.sub_mem _ hφ h2
      have hbot := (carrier_slice_direct_sum hL').2
      have : (eplus ⋆ ψ) ⋆ r ∈ (⊥ : Submodule ℝ W) := by
        rw [← hbot]; exact ⟨h1, h3⟩
      simpa using this
    have hzero' : eplus ⋆ ψ = 0 := by
      have h0 : (0 : W) ⋆ r = 0 := zero_mul_W r
      exact hinj _ hp.1 0 (Submodule.zero_mem _) (by rw [hzero, h0])
    refine ⟨eminus ⋆ ψ, hm, ?_⟩
    have hψeq : ψ = eminus ⋆ ψ := by
      conv_lhs => rw [hsum]
      rw [hzero', zero_add]
    rw [← hψeq, hψr]

/-! ## §33 — the universal axial carrier type -/

/-- **PRINCIPAL THEOREM (§33): `universal_axial_carrier_type`, verdict
`UNIVERSAL AXIAL CARRIER TYPE`.**  For any two minimal carriers there is a Task-12
equivalence which

* maps the plus slice onto the plus slice and the minus slice onto the minus slice,
* intertwines the reference action and the action of every full lift,
* and is compatible with the exact same pair of central sector factors on both sides.

Hence every minimal carrier carries exactly the same intrinsic one-axis transformation
structure; the exact formal criterion is the conjunction below. -/
theorem universal_axial_carrier_type {L L' : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) (hL' : IsMinimalLeftCarrier L') :
    ∃ r : W,
      (∀ ψ ∈ Kplus L, ψ ⋆ r ∈ Kplus L') ∧
      (∀ ψ ∈ Kminus L, ψ ⋆ r ∈ Kminus L') ∧
      (∀ φ ∈ Kplus L', ∃ ψ ∈ Kplus L, ψ ⋆ r = φ) ∧
      (∀ φ ∈ Kminus L', ∃ ψ ∈ Kminus L, ψ ⋆ r = φ) ∧
      (∀ (θ : ℝ) (ψ : W), (Uref θ ⋆ ψ) ⋆ r = Uref θ ⋆ (ψ ⋆ r)) ∧
      (∀ (U : ℝ → W), IsFullLift U → ∀ (θ : ℝ) (ψ : W),
        (U θ ⋆ ψ) ⋆ r = U θ ⋆ (ψ ⋆ r)) ∧
      (∀ (θ : ℝ), (∀ ψ ∈ Kplus L, Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
        (∀ ψ ∈ Kplus L', Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
        (∀ ψ ∈ Kminus L, Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ) ∧
        (∀ ψ ∈ Kminus L', Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ)) := by
  obtain ⟨r, hmap, hinj, hsurj⟩ := minimal_carriers_equivalent hL hL'
  obtain ⟨h1, h2, h3, h4⟩ := carrier_equiv_preserves_slices hL hL' hmap hinj hsurj
  exact ⟨r, h1, h2, h3, h4, fun θ ψ => mul_assoc_W _ _ _,
    fun _ _ θ ψ => mul_assoc_W _ _ _,
    fun θ => reference_action_carrier_independent hL hL' θ⟩

end NullSectorTask13
