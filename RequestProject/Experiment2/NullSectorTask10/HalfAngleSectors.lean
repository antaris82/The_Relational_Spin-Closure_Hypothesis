import RequestProject.Experiment2.NullSectorTask10.StateAction

/-!
# Task 10, Layer 7: distinguished-axis state sectors (§21, §22, §23)

Left multiplication by the already derived transverse generator `R` is compared
with left multiplication by the central element `S`.  The two solution spaces of

```
R ψ = + S ψ,      R ψ = - S ψ
```

are classified: they are nonzero, each of real dimension `4` (equivalently
`Z`-dimension `2`), they intersect trivially and together they span the whole
carrier.  Their transformation factor under the candidate-state action is
computed, and is exactly the transverse *vector* factor at **half** the angle.

Finally §23 is answered: the distinguished axis does select these two sectors,
but the analogous construction along a *transverse* generator does **not**
produce sectors invariant under the state action.  No transverse state
orientation is therefore canonically determined by the present data; an
additional choice would be required, and none is introduced.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## Coordinates of left multiplication by the distinguished axis -/

theorem wA_mul_coord_0 (ψ : W) : (wA ⋆ ψ) 0 = ψ 1 := by simp [wA]
theorem wA_mul_coord_1 (ψ : W) : (wA ⋆ ψ) 1 = ψ 0 := by simp [wA]
theorem wA_mul_coord_2 (ψ : W) : (wA ⋆ ψ) 2 = ψ 4 := by simp [wA]
theorem wA_mul_coord_3 (ψ : W) : (wA ⋆ ψ) 3 = ψ 5 := by simp [wA]
theorem wA_mul_coord_4 (ψ : W) : (wA ⋆ ψ) 4 = ψ 2 := by simp [wA]
theorem wA_mul_coord_5 (ψ : W) : (wA ⋆ ψ) 5 = ψ 3 := by simp [wA]
theorem wA_mul_coord_6 (ψ : W) : (wA ⋆ ψ) 6 = ψ 7 := by simp [wA]
theorem wA_mul_coord_7 (ψ : W) : (wA ⋆ ψ) 7 = ψ 6 := by simp [wA]

/-! ## §21 — the two sectors -/

/-- The solution space of `R ψ = + S ψ`. -/
def SectorPlus : Submodule ℝ W where
  carrier := {ψ | wR ⋆ ψ = wS ⋆ ψ}
  zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero_W]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add_W, mul_add_W, ha, hb]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [mul_smul_W, mul_smul_W, ha]

/-- The solution space of `R ψ = - S ψ`. -/
def SectorMinus : Submodule ℝ W where
  carrier := {ψ | wR ⋆ ψ = -(wS ⋆ ψ)}
  zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero_W, neg_zero]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add_W, mul_add_W, ha, hb, neg_add]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [mul_smul_W, mul_smul_W, ha, smul_neg]

theorem mem_SectorPlus_iff (ψ : W) : ψ ∈ SectorPlus ↔ wR ⋆ ψ = wS ⋆ ψ := Iff.rfl
theorem mem_SectorMinus_iff (ψ : W) : ψ ∈ SectorMinus ↔ wR ⋆ ψ = -(wS ⋆ ψ) := Iff.rfl

/-- **THE SECTORS ARE AXIS EIGENSPACES.**  The condition `R ψ = ± S ψ` is
equivalent to `A ψ = ± ψ`: the sectors are eigenspaces of left multiplication by
the distinguished axis. -/
theorem mem_SectorPlus_iff_axis (ψ : W) : ψ ∈ SectorPlus ↔ wA ⋆ ψ = ψ := by
  rw [mem_SectorPlus_iff]
  constructor
  · intro h
    have h2 : wS ⋆ (wR ⋆ ψ) = wS ⋆ (wS ⋆ ψ) := by rw [h]
    rw [← mul_assoc_W, ← mul_assoc_W, wit8_wS_wR, wit8_wS_wS, neg_mul_W, neg_mul_W,
      one_mul_W] at h2
    exact neg_injective h2
  · intro h
    calc wR ⋆ ψ = wR ⋆ (wA ⋆ ψ) := by rw [h]
    _ = wS ⋆ ψ := by rw [← mul_assoc_W, wit8_wR_wA]

theorem mem_SectorMinus_iff_axis (ψ : W) : ψ ∈ SectorMinus ↔ wA ⋆ ψ = -ψ := by
  rw [mem_SectorMinus_iff]
  constructor
  · intro h
    have h2 : wS ⋆ (wR ⋆ ψ) = wS ⋆ (-(wS ⋆ ψ)) := by rw [h]
    rw [← mul_assoc_W, wit8_wS_wR, neg_mul_W, mul_neg_W, ← mul_assoc_W,
      wit8_wS_wS, neg_mul_W, one_mul_W, neg_neg] at h2
    exact neg_eq_iff_eq_neg.mp h2
  · intro h
    calc wR ⋆ ψ = wR ⋆ (-(wA ⋆ ψ)) := by rw [h, neg_neg]
    _ = -(wS ⋆ ψ) := by rw [mul_neg_W, ← mul_assoc_W, wit8_wR_wA]

/-! ### Coordinate description -/

theorem mem_SectorPlus_iff_coords (ψ : W) :
    ψ ∈ SectorPlus ↔ ψ 1 = ψ 0 ∧ ψ 4 = ψ 2 ∧ ψ 5 = ψ 3 ∧ ψ 7 = ψ 6 := by
  rw [mem_SectorPlus_iff_axis]
  constructor
  · intro h
    exact ⟨by simpa [wA] using congrFun h 0, by simpa [wA] using congrFun h 2,
      by simpa [wA] using congrFun h 3, by simpa [wA] using congrFun h 6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    funext i
    fin_cases i <;> simp [wA] <;>
      first
        | exact h1 | exact h1.symm | exact h2 | exact h2.symm
        | exact h3 | exact h3.symm | exact h4 | exact h4.symm

theorem mem_SectorMinus_iff_coords (ψ : W) :
    ψ ∈ SectorMinus ↔ ψ 1 = -ψ 0 ∧ ψ 4 = -ψ 2 ∧ ψ 5 = -ψ 3 ∧ ψ 7 = -ψ 6 := by
  rw [mem_SectorMinus_iff_axis]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrFun h 0; simpa [wA] using this
    · have := congrFun h 2; simpa [wA] using this
    · have := congrFun h 3; simpa [wA] using this
    · have := congrFun h 6; simpa [wA] using this
  · rintro ⟨h1, h2, h3, h4⟩
    funext i
    fin_cases i <;> simp [wA] <;> first | exact h1 | linarith

/-! ### Explicit spanning families -/

/-- A real spanning family of the `+` sector. -/
noncomputable def sPlusB : Fin 4 → W := ![w1 + wA, wB + wP, wC + wQ, wR + wS]

/-- A real spanning family of the `-` sector. -/
noncomputable def sMinusB : Fin 4 → W := ![w1 - wA, wB - wP, wC - wQ, wR - wS]

theorem SectorPlus_eq_span : SectorPlus = Submodule.span ℝ (Set.range sPlusB) := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨h1, h2, h3, h4⟩ := (mem_SectorPlus_iff_coords ψ).1 hψ
    have hdec : ψ = ψ 0 • sPlusB 0 + ψ 2 • sPlusB 1 + ψ 3 • sPlusB 2 + ψ 6 • sPlusB 3 := by
      funext i
      fin_cases i <;>
        simp [sPlusB, w1, wA, wB, wC, wP, wQ, wR, wS] <;>
        first | exact h1 | exact h2 | exact h3 | exact h4
    rw [hdec]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i <;>
      · rw [SetLike.mem_coe, mem_SectorPlus_iff_coords]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [sPlusB, w1, wA, wB, wC, wP, wQ, wR, wS]

theorem SectorMinus_eq_span : SectorMinus = Submodule.span ℝ (Set.range sMinusB) := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨h1, h2, h3, h4⟩ := (mem_SectorMinus_iff_coords ψ).1 hψ
    have hdec : ψ = ψ 0 • sMinusB 0 + ψ 2 • sMinusB 1 + ψ 3 • sMinusB 2 + ψ 6 • sMinusB 3 := by
      funext i
      fin_cases i <;>
        simp [sMinusB, w1, wA, wB, wC, wP, wQ, wR, wS] <;> linarith
    rw [hdec]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i <;>
      · rw [SetLike.mem_coe, mem_SectorMinus_iff_coords]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [sMinusB, w1, wA, wB, wC, wP, wQ, wR, wS]

theorem sPlusB_indep : LinearIndependent ℝ sPlusB := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h2 := congrFun hg 2
  have h3 := congrFun hg 3
  have h6 := congrFun hg 6
  simp [Fin.sum_univ_four, sPlusB, w1, wA, wB, wC, wP, wQ, wR, wS] at h0 h2 h3 h6
  intro i
  fin_cases i <;> assumption

theorem sMinusB_indep : LinearIndependent ℝ sMinusB := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h2 := congrFun hg 2
  have h3 := congrFun hg 3
  have h6 := congrFun hg 6
  simp [Fin.sum_univ_four, sMinusB, w1, wA, wB, wC, wP, wQ, wR, wS] at h0 h2 h3 h6
  intro i
  fin_cases i <;> assumption

/-- **EXACT REAL DIMENSION OF THE `+` SECTOR.** -/
theorem finrank_SectorPlus : Module.finrank ℝ SectorPlus = 4 := by
  rw [SectorPlus_eq_span, finrank_span_eq_card sPlusB_indep]
  simp

/-- **EXACT REAL DIMENSION OF THE `-` SECTOR.** -/
theorem finrank_SectorMinus : Module.finrank ℝ SectorMinus = 4 := by
  rw [SectorMinus_eq_span, finrank_span_eq_card sMinusB_indep]
  simp

/-- Both sectors are nonzero. -/
theorem SectorPlus_ne_bot : SectorPlus ≠ ⊥ := by
  intro h
  have : Module.finrank ℝ SectorPlus = 4 := finrank_SectorPlus
  rw [h] at this
  simp at this

theorem SectorMinus_ne_bot : SectorMinus ≠ ⊥ := by
  intro h
  have : Module.finrank ℝ SectorMinus = 4 := finrank_SectorMinus
  rw [h] at this
  simp at this

/-! ### The `Z`-structure of the sectors -/

theorem wS_mul_mem_SectorPlus {ψ : W} (hψ : ψ ∈ SectorPlus) : wS ⋆ ψ ∈ SectorPlus := by
  rw [mem_SectorPlus_iff_axis] at hψ ⊢
  rw [← mul_assoc_W, wit8_wA_wS, ← wit8_wS_wA, mul_assoc_W, hψ]

theorem wS_mul_mem_SectorMinus {ψ : W} (hψ : ψ ∈ SectorMinus) : wS ⋆ ψ ∈ SectorMinus := by
  rw [mem_SectorMinus_iff_axis] at hψ ⊢
  rw [← mul_assoc_W, wit8_wA_wS, ← wit8_wS_wA, mul_assoc_W, hψ, mul_neg_W]

/-- **`Z`-DIMENSION TWO.**  The `+` sector is the sum of exactly two `Z`-lines,
whose four real generators are independent. -/
theorem SectorPlus_eq_two_Zlines :
    SectorPlus = Zline (w1 + wA) ⊔ Zline (wB + wP) := by
  have hS1 : wS ⋆ (w1 + wA) = wR + wS := by
    rw [mul_add_W, mul_one_W, wit8_wS_wA]; abel
  have hS2 : wS ⋆ (wB + wP) = -(wC + wQ) := by
    rw [mul_add_W, wit8_wS_wB, wit8_wS_wP]; abel
  have hm1 : w1 + wA ∈ SectorPlus := by
    rw [mem_SectorPlus_iff_coords]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [w1, wA]
  have hm2 : wB + wP ∈ SectorPlus := by
    rw [mem_SectorPlus_iff_coords]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wB, wP]
  apply le_antisymm
  · rw [SectorPlus_eq_span, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · show w1 + wA ∈ _
      exact Submodule.mem_sup_left (self_mem_Zline _)
    · show wB + wP ∈ _
      exact Submodule.mem_sup_right (self_mem_Zline _)
    · show wC + wQ ∈ _
      refine Submodule.mem_sup_right ?_
      have hEq : wC + wQ = -(wS ⋆ (wB + wP)) := by rw [hS2, neg_neg]
      rw [hEq]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
    · show wR + wS ∈ _
      refine Submodule.mem_sup_left ?_
      rw [← hS1]
      exact Submodule.subset_span (by simp)
  · refine sup_le ?_ ?_
    · rw [Zline, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hm1, wS_mul_mem_SectorPlus hm1⟩
    · rw [Zline, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hm2, wS_mul_mem_SectorPlus hm2⟩

/-- **`Z`-DIMENSION TWO**, second sector. -/
theorem SectorMinus_eq_two_Zlines :
    SectorMinus = Zline (w1 - wA) ⊔ Zline (wB - wP) := by
  have hS1 : wS ⋆ (w1 - wA) = -(wR - wS) := by
    rw [sub_eq_add_neg, mul_add_W, mul_one_W, mul_neg_W, wit8_wS_wA]; abel
  have hS2 : wS ⋆ (wB - wP) = wC - wQ := by
    rw [sub_eq_add_neg, mul_add_W, mul_neg_W, wit8_wS_wB, wit8_wS_wP]; abel
  have hm1 : w1 - wA ∈ SectorMinus := by
    rw [mem_SectorMinus_iff_coords]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [w1, wA]
  have hm2 : wB - wP ∈ SectorMinus := by
    rw [mem_SectorMinus_iff_coords]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wB, wP]
  apply le_antisymm
  · rw [SectorMinus_eq_span, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · show w1 - wA ∈ _
      exact Submodule.mem_sup_left (self_mem_Zline _)
    · show wB - wP ∈ _
      exact Submodule.mem_sup_right (self_mem_Zline _)
    · show wC - wQ ∈ _
      refine Submodule.mem_sup_right ?_
      rw [← hS2]
      exact Submodule.subset_span (by simp)
    · show wR - wS ∈ _
      refine Submodule.mem_sup_left ?_
      have hEq : wR - wS = -(wS ⋆ (w1 - wA)) := by rw [hS1, neg_neg]
      rw [hEq]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · refine sup_le ?_ ?_
    · rw [Zline, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hm1, wS_mul_mem_SectorMinus hm1⟩
    · rw [Zline, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hm2, wS_mul_mem_SectorMinus hm2⟩

/-! ### Complementarity -/

theorem SectorPlus_inf_SectorMinus : SectorPlus ⊓ SectorMinus = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  rw [Submodule.mem_inf] at hψ
  obtain ⟨h1, h2⟩ := hψ
  rw [mem_SectorPlus_iff_axis] at h1
  rw [mem_SectorMinus_iff_axis] at h2
  have : ψ = -ψ := h1.symm.trans h2
  have h2ψ : (2 : ℝ) • ψ = 0 := by
    rw [two_smul]
    linear_combination (norm := module) this
  simpa using h2ψ

theorem SectorPlus_sup_SectorMinus : SectorPlus ⊔ SectorMinus = ⊤ := by
  rw [eq_top_iff]
  intro ψ _
  have hplus : (2⁻¹ : ℝ) • (ψ + wA ⋆ ψ) ∈ SectorPlus := by
    apply Submodule.smul_mem
    rw [mem_SectorPlus_iff_axis, mul_add_W, ← mul_assoc_W, wit8_wA_wA, one_mul_W]
    abel
  have hminus : (2⁻¹ : ℝ) • (ψ - wA ⋆ ψ) ∈ SectorMinus := by
    apply Submodule.smul_mem
    rw [mem_SectorMinus_iff_axis, sub_eq_add_neg, mul_add_W, mul_neg_W, ← mul_assoc_W,
      wit8_wA_wA, one_mul_W]
    abel
  have hsum : ψ = (2⁻¹ : ℝ) • (ψ + wA ⋆ ψ) + (2⁻¹ : ℝ) • (ψ - wA ⋆ ψ) := by
    module
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hplus) (Submodule.mem_sup_right hminus)

/-! ## §22 — the half-angle transformation factors -/

theorem ksc_mul_left (a b : ℝ) (x : W) : ksc a b ⋆ x = a • x + b • (wR ⋆ x) := by
  simp only [ksc, add_mul_W, smul_mul_W, one_mul_W]

/-- The transverse **vector** channel factor of Layer 4. -/
noncomputable def vectorFactorMinus (θ : ℝ) : W := zsc (Real.cos θ) (- Real.sin θ)

/-- The transverse **vector** channel factor of Layer 4, other channel. -/
noncomputable def vectorFactorPlus (θ : ℝ) : W := zsc (Real.cos θ) (Real.sin θ)

/-- **THE STATE FACTOR ON THE `+` SECTOR.** -/
theorem StateAction_on_SectorPlus {ψ : W} (hψ : ψ ∈ SectorPlus) (θ : ℝ) :
    StateAction θ ψ = zsc (Real.cos (θ / 2)) (- Real.sin (θ / 2)) ⋆ ψ := by
  rw [StateAction, Ustd, ksc_mul_left, zsc_smul, (mem_SectorPlus_iff ψ).1 hψ]

/-- **THE STATE FACTOR ON THE `-` SECTOR.** -/
theorem StateAction_on_SectorMinus {ψ : W} (hψ : ψ ∈ SectorMinus) (θ : ℝ) :
    StateAction θ ψ = zsc (Real.cos (θ / 2)) (Real.sin (θ / 2)) ⋆ ψ := by
  rw [StateAction, Ustd, ksc_mul_left, zsc_smul, (mem_SectorMinus_iff ψ).1 hψ]
  module

/-- **THE HALF-ANGLE RESULT (§22).**  The state factor on the `+` sector at
angle `θ` is exactly the transverse *vector* factor at angle `θ/2`: the angular
dependence of the sector is half that of the vector channels. -/
theorem halfAngle_SectorPlus {ψ : W} (hψ : ψ ∈ SectorPlus) (θ : ℝ) :
    StateAction θ ψ = vectorFactorMinus (θ / 2) ⋆ ψ :=
  StateAction_on_SectorPlus hψ θ

/-- **THE HALF-ANGLE RESULT (§22), second sector.** -/
theorem halfAngle_SectorMinus {ψ : W} (hψ : ψ ∈ SectorMinus) (θ : ℝ) :
    StateAction θ ψ = vectorFactorPlus (θ / 2) ⋆ ψ :=
  StateAction_on_SectorMinus hψ θ

/-- The two sectors are preserved by the state action. -/
theorem StateAction_mem_SectorPlus {ψ : W} (hψ : ψ ∈ SectorPlus) (θ : ℝ) :
    StateAction θ ψ ∈ SectorPlus := by
  rw [StateAction_on_SectorPlus hψ, zsc_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hψ)
    (Submodule.smul_mem _ _ (wS_mul_mem_SectorPlus hψ))

theorem StateAction_mem_SectorMinus {ψ : W} (hψ : ψ ∈ SectorMinus) (θ : ℝ) :
    StateAction θ ψ ∈ SectorMinus := by
  rw [StateAction_on_SectorMinus hψ, zsc_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hψ)
    (Submodule.smul_mem _ _ (wS_mul_mem_SectorMinus hψ))

/-! ## §23 — is a transverse state orientation selected? -/

/-- **THE §23 VERDICT: NO.**  The analogous eigenspace condition along the
*transverse* generator `B` is **not** preserved by the state action: an explicit
`θ` and `ψ` are exhibited.  Hence the present data single out the distinguished
axis, and no transverse state orientation is canonically determined; a further
choice would be required, and none is made here. -/
theorem no_canonical_transverse_state_orientation :
    ∃ (θ : ℝ) (ψ : W), ψ ≠ 0 ∧ wB ⋆ ψ = ψ ∧ wB ⋆ (StateAction θ ψ) ≠ StateAction θ ψ := by
  refine ⟨Real.pi, w1 + wB, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [w1, wB] at this
  · rw [mul_add_W, mul_one_W, wit8_wB_wB]; abel
  · have hU : Ustd Real.pi = -wR := by
      rw [Ustd, show Real.pi / 2 = Real.pi / 2 from rfl]
      have hc : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
      have hs : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      rw [hc, hs, ksc]
      module
    have hval : StateAction Real.pi (w1 + wB) = wC - wR := by
      rw [StateAction, hU, neg_mul_W, mul_add_W, mul_one_W, wit8_wR_wB]
      abel
    rw [hval]
    intro h
    rw [sub_eq_add_neg, mul_add_W, mul_neg_W, wit8_wB_wC, wit8_wB_wR] at h
    have h2 := congrFun h 3
    simp [wC, wR] at h2
    linarith

end NullSectorTask10
