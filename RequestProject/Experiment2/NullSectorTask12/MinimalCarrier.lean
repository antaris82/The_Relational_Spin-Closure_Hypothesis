import RequestProject.Experiment2.NullSectorTask12.DimensionClassification

/-!
# Task 12, Layer 4: proper carriers, minimality and the minimal-generator criterion
(§9, §14, §16, §17)

Results of this layer, all AXIS-INDEPENDENT:

* **Existence (§9).**  Proper nonzero left carriers exist.
* Every element of a proper left carrier has vanishing central quadratic datum, hence
  every proper nonzero left carrier is exactly a generated carrier of real dimension `4`.
* **Minimality (§8, §17).**  `IsMinimalLeftCarrier L` is *equivalent* to
  `IsProperLeftCarrier L`, and to `L` being nonzero, left-stable and four-dimensional.
  In particular all minimal carriers have the same dimension, namely `4`, and every
  proper nonzero left carrier already *is* minimal.
* **Minimal-generator criterion (§14).**  `Lgen ψ` is minimal iff `ψ ≠ 0` and the
  inherited central quadratic datum of `ψ` vanishes.  The criterion is stated through the
  branch-symmetric predicate `IsNullElt` and is proved equivalent to `Ncand 1 ψ = 0` and
  to `Ncand (-1) ψ = 0`; neither Task-09 branch is preferred (§15).
* **Relation to zero divisors (§16).**  The minimal generators are exactly the nonzero
  elements whose left multiplication operator has nontrivial kernel, equivalently whose
  right multiplication operator has nontrivial kernel.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09

/-! ## Elements of a proper carrier -/

/-- **DERIVED.**  A left carrier containing an invertible element is everything. -/
theorem eq_top_of_hasInverse_mem {L : Submodule ℝ W} (hL : IsLeftCarrier L) {y : W}
    (hy : y ∈ L) (hinv : HasInverse y) : L = ⊤ :=
  top_le_iff.1 (by rw [← Lgen_eq_top_of_hasInverse hinv]; exact Lgen_le hL hy)

/-- **DERIVED.**  Every element of a proper left carrier has vanishing central quadratic
datum. -/
theorem isNullElt_of_mem_proper {L : Submodule ℝ W} (hL : IsLeftCarrier L) (hne : L ≠ ⊤)
    {y : W} (hy : y ∈ L) : IsNullElt y := by
  by_contra h
  exact hne (eq_top_of_hasInverse_mem hL hy ((hasInverse_iff y).2 h))

/-- **DERIVED.**  A proper nonzero left carrier is a generated carrier of dimension
four. -/
theorem proper_eq_Lgen {L : Submodule ℝ W} (hL : IsProperLeftCarrier L) :
    ∃ ψ : W, ψ ≠ 0 ∧ IsNullElt ψ ∧ L = Lgen ψ ∧ Module.finrank ℝ L = 4 := by
  obtain ⟨ψ, hψL, hψ⟩ := hL.1.exists_ne_zero
  have hnull : IsNullElt ψ := isNullElt_of_mem_proper hL.1.1 hL.2 hψL
  have hle : Lgen ψ ≤ L := Lgen_le hL.1.1 hψL
  have h4 : Module.finrank ℝ (Lgen ψ) = 4 := finrank_Lgen_eq_four hψ hnull
  have hub : Module.finrank ℝ L ≤ 4 :=
    finrank_le_four_of_nRe_zero _ (fun y hy => (isNullElt_of_mem_proper hL.1.1 hL.2 hy).1)
  have hlb : 4 ≤ Module.finrank ℝ L := by rw [← h4]; exact Submodule.finrank_mono hle
  have hdim : Module.finrank ℝ L = 4 := le_antisymm hub hlb
  exact ⟨ψ, hψ, hnull, (Submodule.eq_of_le_of_finrank_eq hle (by rw [h4, hdim])).symm, hdim⟩

/-! ## Existence of proper nonzero carriers (§9) -/

/-- **DERIVED (§9).**  Proper nonzero left carriers exist.  The witness is derived from
the algebra alone: any square root of the unit with vanishing unit coordinate produces
one, and no distinguished direction is needed. -/
theorem exists_proper_nonzero_leftCarrier :
    ∃ L : Submodule ℝ W, IsNonzeroLeftCarrier L ∧ L ≠ ⊤ := by
  obtain ⟨-, hne, hnull, -⟩ := halfSum_props wit8_wB_wB (by simp [wB])
  refine ⟨Lgen (halfSum wB), ⟨isLeftCarrier_Lgen _, Lgen_ne_bot hne⟩, ?_⟩
  intro h
  have h4 := finrank_Lgen_eq_four hne hnull
  rw [h] at h4
  simp at h4

/-! ## Minimality -/

/-- **DERIVED.**  A proper nonzero left carrier is minimal. -/
theorem isMinimal_of_proper {L : Submodule ℝ W} (hL : IsProperLeftCarrier L) :
    IsMinimalLeftCarrier L := by
  refine ⟨hL.1, ?_⟩
  intro M hM hML
  by_cases hMbot : M = ⊥
  · exact Or.inl hMbot
  · right
    have hMtop : M ≠ ⊤ := by
      intro h
      exact hL.2 (top_le_iff.1 (h ▸ hML))
    obtain ⟨-, -, -, -, hM4⟩ := proper_eq_Lgen ⟨⟨hM, hMbot⟩, hMtop⟩
    obtain ⟨-, -, -, -, hL4⟩ := proper_eq_Lgen hL
    exact Submodule.eq_of_le_of_finrank_eq hML (by rw [hM4, hL4])

/-- **DERIVED.**  A minimal left carrier is proper. -/
theorem proper_of_isMinimal {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    IsProperLeftCarrier L := by
  refine ⟨hL.1, ?_⟩
  intro htop
  obtain ⟨-, hne, hnull, -⟩ := halfSum_props wit8_wB_wB (by simp [wB])
  have hM : IsLeftCarrier (Lgen (halfSum wB)) := isLeftCarrier_Lgen _
  have h4 : Module.finrank ℝ (Lgen (halfSum wB)) = 4 := finrank_Lgen_eq_four hne hnull
  rcases hL.2 (Lgen (halfSum wB)) hM (by rw [htop]; exact le_top) with h | h
  · exact Lgen_ne_bot hne h
  · rw [h, htop] at h4
    simp at h4

/-- **PRINCIPAL THEOREM (§17).**  Minimality and properness coincide, and every minimal
left carrier has real dimension exactly four. -/
theorem isMinimal_iff_proper (L : Submodule ℝ W) :
    IsMinimalLeftCarrier L ↔ IsProperLeftCarrier L :=
  ⟨proper_of_isMinimal, isMinimal_of_proper⟩

/-- **PRINCIPAL THEOREM (§17).**  The exact minimal nonzero dimension is four; all
minimal left carriers have this same dimension. -/
theorem finrank_of_isMinimal {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Module.finrank ℝ L = 4 := by
  obtain ⟨-, -, -, -, h⟩ := proper_eq_Lgen (proper_of_isMinimal hL)
  exact h

/-- **PRINCIPAL THEOREM (§17).**  Every minimal left carrier is a generated carrier. -/
theorem isMinimal_eq_Lgen {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    ∃ ψ : W, ψ ≠ 0 ∧ IsNullElt ψ ∧ L = Lgen ψ := by
  obtain ⟨ψ, h1, h2, h3, -⟩ := proper_eq_Lgen (proper_of_isMinimal hL)
  exact ⟨ψ, h1, h2, h3⟩

/-- **PRINCIPAL THEOREM (§14): the minimal-generator criterion.**  The generated carrier
of `ψ` is minimal exactly when `ψ` is nonzero with vanishing central quadratic datum. -/
theorem isMinimal_Lgen_iff (ψ : W) :
    IsMinimalLeftCarrier (Lgen ψ) ↔ (ψ ≠ 0 ∧ IsNullElt ψ) := by
  constructor
  · intro h
    obtain ⟨hnz, htop⟩ := proper_of_isMinimal h
    have hψ : ψ ≠ 0 := by
      intro hzero
      exact hnz.2 (by rw [hzero, Lgen_zero])
    exact ⟨hψ, isNullElt_of_mem_proper hnz.1 htop (self_mem_Lgen ψ)⟩
  · rintro ⟨hψ, hnull⟩
    refine isMinimal_of_proper ⟨⟨isLeftCarrier_Lgen ψ, Lgen_ne_bot hψ⟩, ?_⟩
    intro h
    have h4 := finrank_Lgen_eq_four hψ hnull
    rw [h] at h4
    simp at h4

/-- **BRANCH-SYMMETRIC FORM (§15) of the minimal-generator criterion.** -/
theorem isMinimal_Lgen_iff_branches (ψ : W) :
    IsMinimalLeftCarrier (Lgen ψ)
      ↔ (ψ ≠ 0 ∧ Ncand 1 ψ = 0) ∧ (ψ ≠ 0 ∧ Ncand (-1) ψ = 0) := by
  rw [isMinimal_Lgen_iff, isNullElt_iff_Ncand]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, ⟨h1, (null_branch_symmetric ψ).1 h2⟩⟩
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1, h2⟩

/-! ## Relation to zero divisors (§16) -/

/-- **DERIVED (§16).**  The nonzero elements with vanishing central quadratic datum — that
is, exactly the minimal generators — are exactly the nonzero elements whose left
multiplication operator has a nontrivial kernel. -/
theorem isNullElt_iff_exists_kernel {ψ : W} (hψ : ψ ≠ 0) :
    IsNullElt ψ ↔ ∃ φ : W, φ ≠ 0 ∧ ψ ⋆ φ = 0 := by
  constructor
  · intro h
    refine ⟨wconj ψ, ?_, ?_⟩
    · rw [Ne, wconj_eq_zero_iff]; exact hψ
    · rw [mul_wconj]; exact (isNullElt_iff_Ncand ψ).1 h
  · rintro ⟨φ, hφ, hzero⟩
    by_contra h
    obtain ⟨y, -, hy⟩ := (hasInverse_iff ψ).2 h
    refine hφ ?_
    have := congrArg (fun z : W => y ⋆ z) hzero
    simp only [mul_zero_W] at this
    rwa [← mul_assoc_W, hy, one_mul_W] at this

theorem isNullElt_iff_exists_right_kernel {ψ : W} (hψ : ψ ≠ 0) :
    IsNullElt ψ ↔ ∃ φ : W, φ ≠ 0 ∧ φ ⋆ ψ = 0 := by
  constructor
  · intro h
    refine ⟨wconj ψ, ?_, ?_⟩
    · rw [Ne, wconj_eq_zero_iff]; exact hψ
    · rw [wconj_mul]; exact (isNullElt_iff_Ncand ψ).1 h
  · rintro ⟨φ, hφ, hzero⟩
    by_contra h
    obtain ⟨y, hy, -⟩ := (hasInverse_iff ψ).2 h
    refine hφ ?_
    have := congrArg (fun z : W => z ⋆ y) hzero
    simp only [zero_mul_W] at this
    rwa [mul_assoc_W, hy, mul_one_W] at this

/-- **PRINCIPAL SUMMARY (§17).**  The classification of left carriers: a left carrier is
either `⊥`, or the full carrier, or minimal of dimension four; and the minimal ones are
exactly the carriers generated by a nonzero element with vanishing central quadratic
datum. -/
theorem leftCarrier_trichotomy {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    L = ⊥ ∨ L = ⊤ ∨ (IsMinimalLeftCarrier L ∧ Module.finrank ℝ L = 4) := by
  by_cases hbot : L = ⊥
  · exact Or.inl hbot
  by_cases htop : L = ⊤
  · exact Or.inr (Or.inl htop)
  · have hmin := isMinimal_of_proper ⟨⟨hL, hbot⟩, htop⟩
    exact Or.inr (Or.inr ⟨hmin, finrank_of_isMinimal hmin⟩)

end NullSectorTask12
