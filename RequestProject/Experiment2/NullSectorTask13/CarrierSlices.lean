import RequestProject.Experiment2.NullSectorTask13.MinusSectorHardening

/-!
# Task 13, Layer 2: the axis-relative slices of an arbitrary minimal carrier (§7, §8)

`L` is an **arbitrary** minimal left carrier throughout: no idempotent-generated
representative, no axial carrier and no other preferred member of the Task-12 family is
selected (§7).

The two axis-relative slices are defined neutrally as intersections with the inherited
sectors,

`K₊(L) = L ⊓ H₊`,  `K₋(L) = L ⊓ H₋`,

and the inherited `2 + 2` splitting is recorded.  They are *not* called spin components,
and nothing about their later transformation behaviour is assumed here (§8).
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask12

/-! ## §8 — the two slices -/

/-- **§8.  NEUTRAL DEFINITION.**  The plus slice of a carrier. -/
def Kplus (L : Submodule ℝ W) : Submodule ℝ W := L ⊓ Hplus

/-- **§8.  NEUTRAL DEFINITION.**  The minus slice of a carrier. -/
def Kminus (L : Submodule ℝ W) : Submodule ℝ W := L ⊓ Hminus

theorem mem_Kplus_iff (L : Submodule ℝ W) (ψ : W) :
    ψ ∈ Kplus L ↔ ψ ∈ L ∧ wA ⋆ ψ = ψ := by
  rw [Kplus, Submodule.mem_inf, mem_Hplus_iff]

theorem mem_Kminus_iff (L : Submodule ℝ W) (ψ : W) :
    ψ ∈ Kminus L ↔ ψ ∈ L ∧ wA ⋆ ψ = -ψ := by
  rw [Kminus, Submodule.mem_inf, mem_Hminus_iff]

theorem Kplus_le (L : Submodule ℝ W) : Kplus L ≤ L := inf_le_left

theorem Kminus_le (L : Submodule ℝ W) : Kminus L ≤ L := inf_le_left

theorem mem_Hplus_of_mem_Kplus {L : Submodule ℝ W} {ψ : W} (h : ψ ∈ Kplus L) :
    ψ ∈ Hplus := h.2

theorem mem_Hminus_of_mem_Kminus {L : Submodule ℝ W} {ψ : W} (h : ψ ∈ Kminus L) :
    ψ ∈ Hminus := h.2

/-! ## §8 — the inherited exact `2 + 2` structure -/

/-- **INHERITED (Task 12), REUSED (§8): `slice_plus_dim`.**  Every minimal carrier meets
the plus sector in exactly two real dimensions. -/
theorem finrank_Kplus {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Module.finrank ℝ (Kplus L) = 2 := (minimal_inf_sectors hL).1

/-- **INHERITED (Task 12), REUSED (§8): `slice_minus_dim`. -/
theorem finrank_Kminus {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Module.finrank ℝ (Kminus L) = 2 := (minimal_inf_sectors hL).2.1

/-- **INHERITED (Task 12), REUSED (§8): `carrier_slice_direct_sum`.**  An arbitrary
minimal carrier is the internal direct sum of its two axis-relative slices. -/
theorem carrier_slice_direct_sum {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Kplus L ⊔ Kminus L = L ∧ Kplus L ⊓ Kminus L = ⊥ :=
  ⟨(minimal_inf_sectors hL).2.2.1, (minimal_inf_sectors hL).2.2.2⟩

/-- **DERIVED (§8).**  The explicit decomposition of a carrier element into its two
slice components, given by left multiplication with the two axial elements. -/
theorem slice_decomposition {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ L) :
    eplus ⋆ ψ ∈ Kplus L ∧ eminus ⋆ ψ ∈ Kminus L ∧ ψ = eplus ⋆ ψ + eminus ⋆ ψ := by
  refine ⟨⟨hL _ _ hψ, ?_⟩, ⟨hL _ _ hψ, ?_⟩, ?_⟩
  · exact (mem_SectorPlus_iff_eplus _).2 (by rw [← mul_assoc_W, eplus_selfProduct])
  · exact (mem_SectorMinus_iff_eminus _).2 (by rw [← mul_assoc_W, eminus_selfProduct])
  · rw [← add_mul_W, eplus_add_eminus, one_mul_W]

/-- **DERIVED (§8).**  Both slices of a minimal carrier are nonzero: each contains a
nonzero element. -/
theorem exists_ne_zero_Kplus {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    ∃ ψ ∈ Kplus L, ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hbot : Kplus L = ⊥ := by
    ext y
    simp only [Submodule.mem_bot]
    exact ⟨fun hy => hc y hy, fun hy => hy ▸ Submodule.zero_mem _⟩
  have h := finrank_Kplus hL
  rw [hbot] at h
  simp at h

theorem exists_ne_zero_Kminus {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    ∃ ψ ∈ Kminus L, ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hbot : Kminus L = ⊥ := by
    ext y
    simp only [Submodule.mem_bot]
    exact ⟨fun hy => hc y hy, fun hy => hy ▸ Submodule.zero_mem _⟩
  have h := finrank_Kminus hL
  rw [hbot] at h
  simp at h

/-- **DERIVED (§8).**  No minimal carrier lies inside one sector: both slices are proper
nonzero subspaces of the carrier. -/
theorem slices_proper {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Kplus L ≠ ⊥ ∧ Kplus L ≠ L ∧ Kminus L ≠ ⊥ ∧ Kminus L ≠ L := by
  have hp := finrank_Kplus hL
  have hm := finrank_Kminus hL
  have hL4 := finrank_of_isMinimal hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; rw [h] at hp; simp at hp
  · intro h; rw [h, hL4] at hp; norm_num at hp
  · intro h; rw [h] at hm; simp at hm
  · intro h; rw [h, hL4] at hm; norm_num at hm

end NullSectorTask13
