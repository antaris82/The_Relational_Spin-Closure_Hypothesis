import RequestProject.Experiment2.NullSectorTask14.SecondAxisImplementation

/-!
# Task 14, Layer 4 (§15, §16): the second-axis slices of an arbitrary minimal carrier

`L` is an **arbitrary** minimal left carrier throughout.  Nothing is inferred from the
inherited A-axis slice theorem: the whole `2 + 2` structure is re-derived here from two
purely algebraic inputs,

* an element `n` with `n ⋆ n = 1` (the axis), and
* an element `m` with `m ⋆ m = 1` and `n ⋆ m = -(m ⋆ n)` (any anticommuting partner),

and is then instantiated at the independently reconstructed second axis `B`, with partner
`A`.  The abstract section is pure algebra: no spatial direction, no orientation and no
transformation family enters it.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## Algebraic preliminaries: the two eigenspaces of an involutive element -/

/-- **NEUTRAL DEFINITION.**  The `+1` eigenspace of left multiplication by `n`. -/
def Hp (n : W) : Submodule ℝ W where
  carrier := {ψ | n ⋆ ψ = ψ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_add_W, hx, hy]
  zero_mem' := mul_zero_W n
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [mul_smul_W, hx]

/-- **NEUTRAL DEFINITION.**  The `-1` eigenspace of left multiplication by `n`. -/
def Hm (n : W) : Submodule ℝ W where
  carrier := {ψ | n ⋆ ψ = -ψ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_add_W, hx, hy, neg_add]
  zero_mem' := by
    show n ⋆ (0 : W) = -(0 : W)
    rw [mul_zero_W, neg_zero]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [mul_smul_W, hx, smul_neg]

@[simp] theorem mem_Hp_iff (n ψ : W) : ψ ∈ Hp n ↔ n ⋆ ψ = ψ := Iff.rfl
@[simp] theorem mem_Hm_iff (n ψ : W) : ψ ∈ Hm n ↔ n ⋆ ψ = -ψ := Iff.rfl

/-- **NEUTRAL DEFINITION.**  The plus slice of a carrier for the axis `n`. -/
def Kp (n : W) (L : Submodule ℝ W) : Submodule ℝ W := L ⊓ Hp n

/-- **NEUTRAL DEFINITION.**  The minus slice of a carrier for the axis `n`. -/
def Km (n : W) (L : Submodule ℝ W) : Submodule ℝ W := L ⊓ Hm n

theorem mem_Kp_iff (n : W) (L : Submodule ℝ W) (ψ : W) :
    ψ ∈ Kp n L ↔ ψ ∈ L ∧ n ⋆ ψ = ψ := Iff.rfl

theorem mem_Km_iff (n : W) (L : Submodule ℝ W) (ψ : W) :
    ψ ∈ Km n L ↔ ψ ∈ L ∧ n ⋆ ψ = -ψ := Iff.rfl

section Involutive

variable {n : W} (hn : n ⋆ n = w1)
include hn

/-- **DERIVED.**  Explicit splitting of a carrier element into its two `n`-parts. -/
theorem slice_split {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W} (hψ : ψ ∈ L) :
    (2⁻¹ : ℝ) • (ψ + n ⋆ ψ) ∈ Kp n L ∧ (2⁻¹ : ℝ) • (ψ - n ⋆ ψ) ∈ Km n L ∧
      ψ = (2⁻¹ : ℝ) • (ψ + n ⋆ ψ) + (2⁻¹ : ℝ) • (ψ - n ⋆ ψ) := by
  have hnψ : n ⋆ ψ ∈ L := hL n ψ hψ
  refine ⟨⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hψ hnψ), ?_⟩,
    ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hψ hnψ), ?_⟩, by module⟩
  · show n ⋆ ((2⁻¹ : ℝ) • (ψ + n ⋆ ψ)) = (2⁻¹ : ℝ) • (ψ + n ⋆ ψ)
    rw [mul_smul_W, mul_add_W, ← mul_assoc_W, hn, one_mul_W]
    module
  · show n ⋆ ((2⁻¹ : ℝ) • (ψ - n ⋆ ψ)) = -((2⁻¹ : ℝ) • (ψ - n ⋆ ψ))
    rw [mul_smul_W, sub_eq_add_neg, mul_add_W, mul_neg_W, ← mul_assoc_W, hn, one_mul_W]
    module

/-- **DERIVED.**  The two slices intersect trivially. -/
theorem Kp_inf_Km (L : Submodule ℝ W) : Kp n L ⊓ Km n L = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro ψ hψ
  rw [Submodule.mem_inf] at hψ
  obtain ⟨⟨-, hp⟩, ⟨-, hm⟩⟩ := hψ
  simp only [Submodule.mem_bot]
  have hp' : n ⋆ ψ = ψ := hp
  have hm' : n ⋆ ψ = -ψ := hm
  have hself : ψ = -ψ := hp'.symm.trans hm'
  have hzz : ψ + ψ = 0 := by rw [add_eq_zero_iff_eq_neg]; exact hself
  have htwo : (2 : ℝ) • ψ = 0 := by rw [two_smul]; exact hzz
  rcases smul_eq_zero.mp htwo with h | h
  · norm_num at h
  · exact h

/-- **DERIVED.**  The two slices span the carrier. -/
theorem Kp_sup_Km {L : Submodule ℝ W} (hL : IsLeftCarrier L) : Kp n L ⊔ Km n L = L := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  intro ψ hψ
  obtain ⟨h1, h2, h3⟩ := slice_split hn hL hψ
  rw [h3]
  exact Submodule.add_mem_sup h1 h2

end Involutive

section Partner

variable {n m : W} (hn : n ⋆ n = w1) (hm : m ⋆ m = w1) (hnm : n ⋆ m = -(m ⋆ n))
include hn hm hnm

omit hn hm in
/-- **DERIVED.**  An anticommuting partner exchanges the two slices. -/
theorem partner_mem_Km {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kp n L) : m ⋆ ψ ∈ Km n L := by
  refine ⟨hL m ψ hψ.1, ?_⟩
  show n ⋆ (m ⋆ ψ) = -(m ⋆ ψ)
  rw [← mul_assoc_W, hnm, neg_mul_W, mul_assoc_W, hψ.2]

omit hn hm in
theorem partner_mem_Kp {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Km n L) : m ⋆ ψ ∈ Kp n L := by
  refine ⟨hL m ψ hψ.1, ?_⟩
  show n ⋆ (m ⋆ ψ) = m ⋆ ψ
  rw [← mul_assoc_W, hnm, neg_mul_W, mul_assoc_W, hψ.2, mul_neg_W, neg_neg]

/-- **DERIVED.**  The two slices are linearly isomorphic. -/
noncomputable def sliceEquiv {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    Kp n L ≃ₗ[ℝ] Km n L where
  toFun ψ := ⟨m ⋆ (ψ : W), partner_mem_Km hnm hL ψ.2⟩
  map_add' := by intro x y; apply Subtype.ext; simpa using mul_add_W m x y
  map_smul' := by intro c x; apply Subtype.ext; simpa using mul_smul_W c m x
  invFun ψ := ⟨m ⋆ (ψ : W), partner_mem_Kp hnm hL ψ.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    show m ⋆ (m ⋆ (x : W)) = (x : W)
    rw [← mul_assoc_W, hm, one_mul_W]
  right_inv := by
    intro x
    apply Subtype.ext
    show m ⋆ (m ⋆ (x : W)) = (x : W)
    rw [← mul_assoc_W, hm, one_mul_W]

set_option maxHeartbeats 1000000 in
/-- **DERIVED.**  Both slices of a minimal carrier have real dimension two. -/
theorem finrank_slices {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Module.finrank ℝ (Kp n L) = 2 ∧ Module.finrank ℝ (Km n L) = 2 := by
  have hLc : IsLeftCarrier L := hL.1.1
  have heq : Module.finrank ℝ (Kp n L) = Module.finrank ℝ (Km n L) :=
    LinearEquiv.finrank_eq (sliceEquiv hm hnm hLc)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Kp n L) (Km n L)
  rw [Kp_sup_Km hn hLc, Kp_inf_Km hn L, finrank_of_isMinimal hL] at hsum
  simp only [finrank_bot, add_zero] at hsum
  constructor <;> omega

end Partner

/-! ## §15 — the second-axis slices -/

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§15).**  The two second-axis sectors. -/
abbrev HBplus : Submodule ℝ W := Hp wB

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§15).** -/
abbrev HBminus : Submodule ℝ W := Hm wB

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§15).**  The plus slice of a carrier for the
second axis. -/
abbrev KBplus (L : Submodule ℝ W) : Submodule ℝ W := Kp wB L

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§15).** -/
abbrev KBminus (L : Submodule ℝ W) : Submodule ℝ W := Km wB L

theorem wB_sq : wB ⋆ wB = w1 := wit8_wB_wB

theorem wA_sq : wA ⋆ wA = w1 := wit8_wA_wA

theorem wA_wB_anticomm : wB ⋆ wA = -(wA ⋆ wB) := by
  rw [wit8_wB_wA, wit8_wA_wB]

/-- **PRINCIPAL THEOREM (§15): `second_axis_sector_split`.**  For an *arbitrary* minimal
left carrier the two second-axis slices are complementary and span the carrier. -/
theorem second_axis_carrier_split {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    KBplus L ⊓ KBminus L = ⊥ ∧ KBplus L ⊔ KBminus L = L :=
  ⟨Kp_inf_Km wB_sq L, Kp_sup_Km wB_sq hL.1.1⟩

/-- **PRINCIPAL THEOREM (§15): `second_axis_slice_dimensions`.**  Each second-axis slice of
an arbitrary minimal carrier has real dimension exactly two.  Proved from the second axis
itself, not inferred from the inherited A-axis theorem. -/
theorem second_axis_slice_dimensions {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Module.finrank ℝ (KBplus L) = 2 ∧ Module.finrank ℝ (KBminus L) = 2 :=
  finrank_slices wB_sq wA_sq wA_wB_anticomm hL

/-! ## §16 — the central structure of the second-axis slices -/

section CentralLines

variable {n : W}

/-- **DERIVED (§16).**  Each slice is stable under the exact center. -/
theorem wS_mul_mem_Kp {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kp n L) : wS ⋆ ψ ∈ Kp n L := by
  refine ⟨hL wS ψ hψ.1, ?_⟩
  show n ⋆ (wS ⋆ ψ) = wS ⋆ ψ
  rw [← mul_assoc_W, ← wS_central n, mul_assoc_W, hψ.2]

theorem wS_mul_mem_Km {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Km n L) : wS ⋆ ψ ∈ Km n L := by
  refine ⟨hL wS ψ hψ.1, ?_⟩
  show n ⋆ (wS ⋆ ψ) = -(wS ⋆ ψ)
  rw [← mul_assoc_W, ← wS_central n, mul_assoc_W, hψ.2, mul_neg_W]

end CentralLines

/-- **DERIVED (§16).**  A two-dimensional subspace stable under the exact center is the
central line of any of its nonzero elements: there is no preferred generator. -/
theorem central_line_of_finrank_two {K : Submodule ℝ W}
    (hdim : Module.finrank ℝ K = 2) (hstab : ∀ ψ ∈ K, wS ⋆ ψ ∈ K) {ψ : W} (hψ : ψ ∈ K)
    (hne : ψ ≠ 0) : K = Zspan ψ := by
  have hle : Zspan ψ ≤ K := by
    rw [Zspan, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hψ
    · exact hstab ψ hψ
  have h2 : Module.finrank ℝ (Zspan ψ) = 2 := finrank_Zspan hne
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, hdim])).symm

/-- **PRINCIPAL THEOREM (§16): `second_axis_slices_are_central_lines`.**  For an arbitrary
minimal carrier both second-axis slices are single lines over the exact center: each equals
the central plane of *any* of its nonzero elements, so no preferred nonzero vector is
selected. -/
theorem second_axis_slices_central_lines {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ χ : W} (hψ : ψ ∈ KBplus L) (hψ0 : ψ ≠ 0) (hχ : χ ∈ KBminus L) (hχ0 : χ ≠ 0) :
    KBplus L = Zspan ψ ∧ KBminus L = Zspan χ := by
  have hLc : IsLeftCarrier L := hL.1.1
  obtain ⟨hp, hm⟩ := second_axis_slice_dimensions hL
  exact ⟨central_line_of_finrank_two hp (fun _ h => wS_mul_mem_Kp hLc h) hψ hψ0,
    central_line_of_finrank_two hm (fun _ h => wS_mul_mem_Km hLc h) hχ hχ0⟩

/-- **DERIVED (§15).**  Both second-axis slices of a minimal carrier are nonzero. -/
theorem second_axis_slices_ne_bot {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    (∃ ψ ∈ KBplus L, ψ ≠ 0) ∧ (∃ χ ∈ KBminus L, χ ≠ 0) := by
  obtain ⟨hp, hm⟩ := second_axis_slice_dimensions hL
  constructor
  · by_contra hcon
    push_neg at hcon
    have : KBplus L = ⊥ := by
      refine le_antisymm (fun ψ hψ => ?_) bot_le
      simpa using hcon ψ hψ
    rw [this, finrank_bot] at hp
    exact absurd hp (by norm_num)
  · by_contra hcon
    push_neg at hcon
    have : KBminus L = ⊥ := by
      refine le_antisymm (fun ψ hψ => ?_) bot_le
      simpa using hcon ψ hψ
    rw [this, finrank_bot] at hm
    exact absurd hm (by norm_num)

end NullSectorTask14
