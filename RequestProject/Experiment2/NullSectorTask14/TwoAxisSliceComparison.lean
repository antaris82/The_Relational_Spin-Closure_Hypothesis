import RequestProject.Experiment2.NullSectorTask14.SecondAxisSectorAction

/-!
# Task 14, Layer 6 (§19, §20): the first two-axis comparison on one carrier

Both one-axis systems are now available *independently*.  This module places them side by
side on one and the same arbitrary minimal carrier and classifies the four mixed slice
intersections

`K_{n,σ}(L) ∩ K_{m,τ}(L)`,   `σ, τ ∈ {+,-}`.

The result is not assumed: the intersections are computed from the anticommutation
relation alone, and the exact exceptional condition (`n` and `m` commuting instead of
anticommuting) is recorded separately.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

section AnticommutingPair

variable {n m : W} (hnm : n ⋆ m = -(m ⋆ n))
include hnm

private theorem two_smul_eq_zero_imp {ψ : W} (h : ψ = -ψ) : ψ = 0 := by
  have hzz : ψ + ψ = 0 := by rw [add_eq_zero_iff_eq_neg]; exact h
  have htwo : (2 : ℝ) • ψ = 0 := by rw [two_smul]; exact hzz
  rcases smul_eq_zero.mp htwo with hc | hc
  · norm_num at hc
  · exact hc

/-- **DERIVED (§20).**  If two axis elements anticommute, no nonzero carrier element is a
simultaneous eigenvector: the four mixed intersections all vanish.  Stated first for the
two `+` slices. -/
theorem mixed_slice_pp (L : Submodule ℝ W) : Kp n L ⊓ Kp m L = ⊥ := by
  refine le_antisymm (fun ψ hψ => ?_) bot_le
  rw [Submodule.mem_inf] at hψ
  obtain ⟨⟨-, hn'⟩, ⟨-, hm'⟩⟩ := hψ
  have hn2 : n ⋆ ψ = ψ := hn'
  have hm2 : m ⋆ ψ = ψ := hm'
  have h1 : (n ⋆ m) ⋆ ψ = ψ := by rw [mul_assoc_W, hm2, hn2]
  have h2 : (m ⋆ n) ⋆ ψ = ψ := by rw [mul_assoc_W, hn2, hm2]
  simp only [Submodule.mem_bot]
  have hkey : (n ⋆ m) ⋆ ψ = (-(m ⋆ n)) ⋆ ψ := by rw [hnm]
  rw [h1, neg_mul_W, h2] at hkey
  exact two_smul_eq_zero_imp hnm hkey

theorem mixed_slice_pm (L : Submodule ℝ W) : Kp n L ⊓ Km m L = ⊥ := by
  refine le_antisymm (fun ψ hψ => ?_) bot_le
  rw [Submodule.mem_inf] at hψ
  obtain ⟨⟨-, hn'⟩, ⟨-, hm'⟩⟩ := hψ
  have hn2 : n ⋆ ψ = ψ := hn'
  have hm2 : m ⋆ ψ = -ψ := hm'
  have h1 : (n ⋆ m) ⋆ ψ = -ψ := by rw [mul_assoc_W, hm2, mul_neg_W, hn2]
  have h2 : (m ⋆ n) ⋆ ψ = -ψ := by rw [mul_assoc_W, hn2, hm2]
  simp only [Submodule.mem_bot]
  have hkey : (n ⋆ m) ⋆ ψ = (-(m ⋆ n)) ⋆ ψ := by rw [hnm]
  rw [h1, neg_mul_W, h2] at hkey
  have hneg : -ψ = 0 := two_smul_eq_zero_imp hnm hkey
  simpa using hneg

theorem mixed_slice_mp (L : Submodule ℝ W) : Km n L ⊓ Kp m L = ⊥ := by
  refine le_antisymm (fun ψ hψ => ?_) bot_le
  rw [Submodule.mem_inf] at hψ
  obtain ⟨⟨-, hn'⟩, ⟨-, hm'⟩⟩ := hψ
  have hn2 : n ⋆ ψ = -ψ := hn'
  have hm2 : m ⋆ ψ = ψ := hm'
  have h1 : (n ⋆ m) ⋆ ψ = -ψ := by rw [mul_assoc_W, hm2, hn2]
  have h2 : (m ⋆ n) ⋆ ψ = -ψ := by rw [mul_assoc_W, hn2, mul_neg_W, hm2]
  simp only [Submodule.mem_bot]
  have hkey : (n ⋆ m) ⋆ ψ = (-(m ⋆ n)) ⋆ ψ := by rw [hnm]
  rw [h1, neg_mul_W, h2] at hkey
  have hneg : -ψ = 0 := two_smul_eq_zero_imp hnm hkey
  simpa using hneg

theorem mixed_slice_mm (L : Submodule ℝ W) : Km n L ⊓ Km m L = ⊥ := by
  refine le_antisymm (fun ψ hψ => ?_) bot_le
  rw [Submodule.mem_inf] at hψ
  obtain ⟨⟨-, hn'⟩, ⟨-, hm'⟩⟩ := hψ
  have hn2 : n ⋆ ψ = -ψ := hn'
  have hm2 : m ⋆ ψ = -ψ := hm'
  have h1 : (n ⋆ m) ⋆ ψ = ψ := by rw [mul_assoc_W, hm2, mul_neg_W, hn2, neg_neg]
  have h2 : (m ⋆ n) ⋆ ψ = ψ := by rw [mul_assoc_W, hn2, mul_neg_W, hm2, neg_neg]
  simp only [Submodule.mem_bot]
  have hkey : (n ⋆ m) ⋆ ψ = (-(m ⋆ n)) ⋆ ψ := by rw [hnm]
  rw [h1, neg_mul_W, h2] at hkey
  exact two_smul_eq_zero_imp hnm hkey

end AnticommutingPair

/-! ## §20 — the two independently reconstructed axes on one carrier -/

/-- **PRINCIPAL THEOREM (§20): `two_axis_slice_intersections`.**  On an *arbitrary* minimal
left carrier the four intersections of the A-slices with the independently reconstructed
B-slices are all zero.  Nothing was assumed: the vanishing follows from the inherited
anticommutation `A ⋆ B = -(B ⋆ A)` alone. -/
theorem two_axis_slice_intersections (L : Submodule ℝ W) :
    Kp wA L ⊓ KBplus L = ⊥ ∧ Kp wA L ⊓ KBminus L = ⊥ ∧
    Km wA L ⊓ KBplus L = ⊥ ∧ Km wA L ⊓ KBminus L = ⊥ := by
  have hAB : wA ⋆ wB = -(wB ⋆ wA) := by rw [wit8_wA_wB, wit8_wB_wA, neg_neg]
  exact ⟨mixed_slice_pp hAB L, mixed_slice_pm hAB L, mixed_slice_mp hAB L,
    mixed_slice_mm hAB L⟩

/-- **DERIVED (§20), the exceptional case.**  The vanishing is genuinely a consequence of
anticommutation: for one and the same axis the corresponding intersection is the whole
slice, which for a minimal carrier is two-dimensional, not zero. -/
theorem same_axis_slice_intersection {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Kp wA L ⊓ Kp wA L = Kp wA L ∧ Module.finrank ℝ (Kp wA L) = 2 :=
  ⟨inf_idem _, (finrank_slices wA_sq wB_sq (by rw [wit8_wA_wB, wit8_wB_wA, neg_neg]) hL).1⟩

/-- **DERIVED (§20).**  The two decompositions of one carrier are therefore genuinely
different: each is a `2 + 2` splitting, and no nonzero element of the carrier belongs to
both an A-slice and a B-slice. -/
theorem two_axis_decompositions_transverse {L : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) :
    (Kp wA L ⊔ Km wA L = L) ∧ (KBplus L ⊔ KBminus L = L) ∧
    (∀ ψ : W, ψ ∈ Kp wA L → ψ ∈ KBplus L → ψ = 0) := by
  refine ⟨Kp_sup_Km wA_sq hL.1.1, (second_axis_carrier_split hL).2, fun ψ h1 h2 => ?_⟩
  have hmem : ψ ∈ Kp wA L ⊓ KBplus L := ⟨h1, h2⟩
  rw [(two_axis_slice_intersections L).1] at hmem
  simpa using hmem

end NullSectorTask14
