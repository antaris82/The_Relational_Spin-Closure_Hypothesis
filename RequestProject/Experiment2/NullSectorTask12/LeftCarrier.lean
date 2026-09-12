import RequestProject.Experiment2.NullSectorTask12.SafeBase

/-!
# Task 12, Layer 1: left-stable carriers (§6–§8)

Neutral definitions only.  A *left carrier* is a real subspace of the inherited carrier
`W` that absorbs multiplication by every element of `W` on the left.  Nothing is called a
representation or a module of any conventional kind here, and no minimality outcome is
assumed.

Status: DERIVED (definitions), the two extreme examples `⊥` and `⊤` are LEFT-STABLE.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09

/-- **§6.  NEUTRAL DEFINITION.**  A real subspace `L ⊆ W` is *left-stable* when
`x ⋆ ψ ∈ L` for every `x : W` and every `ψ ∈ L`. -/
def IsLeftCarrier (L : Submodule ℝ W) : Prop := ∀ x ψ : W, ψ ∈ L → x ⋆ ψ ∈ L

/-- **§7.  NONTRIVIALITY.** -/
def IsNonzeroLeftCarrier (L : Submodule ℝ W) : Prop := IsLeftCarrier L ∧ L ≠ ⊥

/-- **§7.  PROPER CARRIER.**  A nonzero left carrier different from the full carrier. -/
def IsProperLeftCarrier (L : Submodule ℝ W) : Prop := IsNonzeroLeftCarrier L ∧ L ≠ ⊤

/-- **§8.  MINIMALITY.**  Intrinsic: no left-stable subspace strictly between `⊥` and
`L`. -/
def IsMinimalLeftCarrier (L : Submodule ℝ W) : Prop :=
  IsNonzeroLeftCarrier L ∧ ∀ M : Submodule ℝ W, IsLeftCarrier M → M ≤ L → M = ⊥ ∨ M = L

theorem isLeftCarrier_bot : IsLeftCarrier (⊥ : Submodule ℝ W) := by
  intro x ψ hψ
  rw [Submodule.mem_bot] at hψ
  rw [hψ, mul_zero_W]
  exact Submodule.zero_mem _

theorem isLeftCarrier_top : IsLeftCarrier (⊤ : Submodule ℝ W) := by
  intro _ _ _; trivial

theorem IsMinimalLeftCarrier.isNonzero {L : Submodule ℝ W} (h : IsMinimalLeftCarrier L) :
    IsNonzeroLeftCarrier L := h.1

theorem IsNonzeroLeftCarrier.exists_ne_zero {L : Submodule ℝ W}
    (h : IsNonzeroLeftCarrier L) : ∃ ψ ∈ L, ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h.2 (by
    ext y
    simp only [Submodule.mem_bot]
    exact ⟨fun hy => hc y hy, fun hy => hy ▸ Submodule.zero_mem _⟩)

end NullSectorTask12
