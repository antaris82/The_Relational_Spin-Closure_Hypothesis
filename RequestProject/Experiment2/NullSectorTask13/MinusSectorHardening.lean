import RequestProject.Experiment2.NullSectorTask13.SafeBase

/-!
# Task 13, Layer 1: the minus-sector hardening obligation (§1)

Task 12 proved, for the plus sector `H₊ = {ψ | A ⋆ ψ = ψ}`, that

* `H₊` is not a left carrier;
* the exact left stabilizer `StabL H₊` is the kernel of the compression
  `x ↦ e₋ ⋆ x ⋆ e₊` and has real dimension `6`;
* `H₊` is reducible under that exact stabilizer.

The corresponding statements for

`H₋ = {ψ | A ⋆ ψ = -ψ}`

were left open.  **This module closes them, by proof and not by an appeal to an expected
`+ ↔ −` symmetry.**  Every statement below is derived from the inherited multiplication
and the defining sector relation of `H₋`.

Only *after* this module may symmetric plus/minus language be used downstream (§1).

## Results (all DERIVED, AXIS-RELATIVE)

* `StabL_Hminus_eq_ker` — the exact left stabilizer of `H₋` is the kernel of the opposite
  compression `x ↦ e₊ ⋆ x ⋆ e₋`;
* `mem_StabL_Hminus_iff_coords` / `mem_StabL_Hplus_iff_coords` — exact coordinate
  characterizations: two linear equations each;
* `stabMinus_span` and `finrank_StabL_Hminus` — an exact six-element basis and the exact
  real dimension `6`;
* `StabL_Hminus_algebra` — it is a subalgebra containing the unit, the center and the
  axis, but not the transverse generator `B`;
* `conj_wB_StabL_iff` — the exact structural relation with `StabL H₊`: the inherited
  inner automorphism `x ↦ B ⋆ x ⋆ B` carries one stabilizer onto the other;
* `Hminus_reducible` — an explicit proper nonzero invariant subspace, hence `H₋` is
  **REDUCIBLE** under its exact left stabilizer.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask12

/-! ## The opposite compression -/

/-- The compression operator measuring the failure of left stability of the minus
sector. -/
noncomputable def crossMP : W →ₗ[ℝ] W := (Lmul eplus).comp (Rmul eminus)

@[simp] theorem crossMP_apply (x : W) : crossMP x = eplus ⋆ (x ⋆ eminus) := rfl

theorem crossMP_idem (x : W) : crossMP (crossMP x) = crossMP x := by
  simp only [crossMP_apply]
  rw [mul_assoc_W eplus (x ⋆ eminus) eminus, mul_assoc_W x eminus eminus,
    eminus_selfProduct, ← mul_assoc_W eplus eplus (x ⋆ eminus), eplus_selfProduct]

/-- **DERIVED.**  The exact coordinates of the opposite compression. -/
theorem crossMP_coords (x : W) :
    crossMP x = ![0, 0, (x 2 + x 4) / 2, (x 3 + x 5) / 2, (x 2 + x 4) / 2,
      (x 3 + x 5) / 2, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [crossMP, eplus, eminus, esph, wit8MulFun] <;> ring

/-- **DERIVED.**  The exact coordinates of the Task-12 compression. -/
theorem crossPM_coords (x : W) :
    crossPM x = ![0, 0, (x 2 - x 4) / 2, (x 3 - x 5) / 2, -((x 2 - x 4) / 2),
      -((x 3 - x 5) / 2), 0, 0] := by
  funext i
  fin_cases i <;>
    simp [crossPM, eplus, eminus, esph, wit8MulFun] <;> ring

/-! ## §1.1 — the exact left stabilizer of the minus sector -/

/-- **DERIVED (§1).**  The exact left stabilizer of the minus sector is the kernel of the
opposite compression `x ↦ e₊ ⋆ x ⋆ e₋`. -/
theorem StabL_Hminus_eq_ker : StabL Hminus = LinearMap.ker crossMP := by
  ext x
  simp only [mem_StabL_iff, LinearMap.mem_ker, crossMP_apply]
  constructor
  · intro hx
    have hmem : eminus ∈ Hminus := by
      rw [mem_SectorMinus_iff_eminus]; exact eminus_selfProduct
    have h1 := (mem_SectorMinus_iff_eminus _).1 (hx eminus hmem)
    have hsplit : eplus ⋆ (x ⋆ eminus) = (w1 - eminus) ⋆ (x ⋆ eminus) := by
      have : eplus = w1 - eminus := by
        rw [← eplus_add_eminus]; abel
      rw [this]
    rw [hsplit, sub_eq_add_neg, add_mul_W, one_mul_W, neg_mul_W, h1]
    abel
  · intro hx ψ hψ
    obtain ⟨y, rfl⟩ : ∃ y : W, eminus ⋆ y = ψ := by
      have hψ' : ψ ∈ LinearMap.range (Lmul eminus) := by
        rw [← SectorMinus_eq_range]; exact hψ
      exact hψ'
    have hxe : eminus ⋆ (x ⋆ eminus) = x ⋆ eminus := by
      have hsplit : (w1 : W) ⋆ (x ⋆ eminus) = (eminus + eplus) ⋆ (x ⋆ eminus) := by
        rw [add_comm, eplus_add_eminus]
      rw [one_mul_W, add_mul_W, hx, add_zero] at hsplit
      exact hsplit.symm
    have hmem : x ⋆ eminus ∈ Hminus := (mem_SectorMinus_iff_eminus _).2 hxe
    have := mul_right_mem_SectorMinus hmem y
    rwa [mul_assoc_W] at this

/-! ## §1.3 — exact coordinate characterizations -/

/-- **DERIVED (§1.3).**  Exact coordinate characterization of the left stabilizer of the
minus sector: two linear equations. -/
theorem mem_StabL_Hminus_iff_coords (x : W) :
    x ∈ StabL Hminus ↔ x 2 + x 4 = 0 ∧ x 3 + x 5 = 0 := by
  rw [StabL_Hminus_eq_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    rw [crossMP_coords] at h2 h3
    simp at h2 h3
    constructor <;> linarith
  · rintro ⟨h2, h3⟩
    rw [crossMP_coords]
    funext i
    fin_cases i <;> simp [h2, h3]

/-- **DERIVED (§1.3).**  Exact coordinate characterization of the Task-12 stabilizer of
the plus sector, for comparison: the two opposite linear equations. -/
theorem mem_StabL_Hplus_iff_coords (x : W) :
    x ∈ StabL Hplus ↔ x 2 - x 4 = 0 ∧ x 3 - x 5 = 0 := by
  rw [StabL_SectorPlus_eq_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    rw [crossPM_coords] at h2 h3
    simp at h2 h3
    constructor <;> linarith
  · rintro ⟨h2, h3⟩
    rw [crossPM_coords]
    funext i
    fin_cases i <;> simp [h2, h3]

/-! ## §1.1 and §1.3 — an exact basis and the exact dimension -/

/-- An explicit six-element family inside the left stabilizer of the minus sector. -/
noncomputable def stabMinusB : Fin 6 → W := ![w1, wA, wB - wP, wC - wQ, wR, wS]

theorem stabMinusB_mem (i : Fin 6) : stabMinusB i ∈ StabL Hminus := by
  fin_cases i <;>
    · rw [mem_StabL_Hminus_iff_coords]
      constructor <;> simp [stabMinusB, w1, wA, wB, wC, wP, wQ, wR, wS]

theorem stabMinusB_indep : LinearIndependent ℝ stabMinusB := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  have h2 := congrFun hg 2
  have h3 := congrFun hg 3
  have h6 := congrFun hg 6
  have h7 := congrFun hg 7
  simp [Fin.sum_univ_six, stabMinusB, w1, wA, wB, wC, wP, wQ, wR, wS] at h0 h1 h2 h3 h6 h7
  intro i
  fin_cases i <;> assumption

/-- **DERIVED (§1.3).**  The exact left stabilizer of the minus sector is spanned by the
explicit six-element family. -/
theorem StabL_Hminus_eq_span :
    StabL Hminus = Submodule.span ℝ (Set.range stabMinusB) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h2, h3⟩ := (mem_StabL_Hminus_iff_coords x).1 hx
    have hdec : x = x 0 • stabMinusB 0 + x 1 • stabMinusB 1 + x 2 • stabMinusB 2
        + x 3 • stabMinusB 3 + x 6 • stabMinusB 4 + x 7 • stabMinusB 5 := by
      funext i
      fin_cases i <;>
        simp [stabMinusB, w1, wA, wB, wC, wP, wQ, wR, wS] <;> linarith
    rw [hdec]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact stabMinusB_mem i

/-- **PRINCIPAL THEOREM (§1.1): `minus_sector_stabilizer_exact`.**  The exact left
stabilizer of the minus sector has real dimension six — the same codimension-two failure
of left stability as on the plus side, now proved and not inferred. -/
theorem finrank_StabL_Hminus : Module.finrank ℝ (StabL Hminus) = 6 := by
  rw [StabL_Hminus_eq_span, finrank_span_eq_card stabMinusB_indep]
  simp

/-! ## §1.2 — the stabilizer is a subalgebra -/

/-- **DERIVED (§1.2).**  The exact left stabilizer of the minus sector is closed under
multiplication and contains the unit, the center and the distinguished axis, but not the
transverse generator `B`. -/
theorem StabL_Hminus_algebra :
    w1 ∈ StabL Hminus ∧ wS ∈ StabL Hminus ∧ wA ∈ StabL Hminus ∧
      wB ∉ StabL Hminus ∧
      ∀ x ∈ StabL Hminus, ∀ y ∈ StabL Hminus, x ⋆ y ∈ StabL Hminus := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_StabL_Hminus_iff_coords]; constructor <;> simp [w1]
  · rw [mem_StabL_Hminus_iff_coords]; constructor <;> simp [wS]
  · rw [mem_StabL_Hminus_iff_coords]; constructor <;> simp [wA]
  · rw [mem_StabL_Hminus_iff_coords]
    intro h
    have := h.1
    simp [wB] at this
  · intro x hx y hy ψ hψ
    rw [mul_assoc_W]
    exact hx _ (hy ψ hψ)

/-- **DERIVED (§1.2).**  The minus sector is not a left carrier either — the exact
counterpart of the Task-12 negative result, proved from the coordinate characterization
of its stabilizer. -/
theorem not_isLeftCarrier_Hminus : ¬ IsLeftCarrier Hminus :=
  not_isLeftCarrier_SectorMinus

/-! ## §1.4 — the exact structural relation with the plus stabilizer -/

/-- The inherited inner transformation by the transverse generator `B`. -/
noncomputable def conjB (x : W) : W := wB ⋆ (x ⋆ wB)

theorem conjB_coords (x : W) :
    conjB x = ![x 0, -x 1, x 2, -x 3, -x 4, x 5, -x 6, x 7] := by
  funext i
  fin_cases i <;> simp [conjB, wB, wit8MulFun]

/-- **DERIVED.**  The inner transformation by `B` is an involution. -/
theorem conjB_conjB (x : W) : conjB (conjB x) = x := by
  funext i
  fin_cases i <;> simp [conjB_coords]

/-- **DERIVED.**  The inner transformation by `B` is multiplicative: it is an algebra
automorphism of the inherited carrier. -/
theorem conjB_mul (x y : W) : conjB (x ⋆ y) = conjB x ⋆ conjB y := by
  funext i
  fin_cases i <;> simp [conjB, wB, wit8MulFun] <;> ring

/-- **DERIVED.**  The inner transformation by `B` reverses the axis. -/
theorem conjB_wA : conjB wA = -wA := by
  funext i; fin_cases i <;> simp [conjB_coords, wA]

/-- **PRINCIPAL THEOREM (§1.4): the two stabilizers are structurally related.**  The
inherited inner automorphism `x ↦ B ⋆ x ⋆ B`, which reverses the selected axis, carries
the exact left stabilizer of the plus sector bijectively onto the exact left stabilizer
of the minus sector.  The `+ ↔ −` symmetry is therefore not an assumption but an
inherited inner symmetry of the algebra. -/
theorem conjB_StabL_iff (x : W) : x ∈ StabL Hminus ↔ conjB x ∈ StabL Hplus := by
  rw [mem_StabL_Hminus_iff_coords, mem_StabL_Hplus_iff_coords]
  have e2 : conjB x 2 = x 2 := by rw [conjB_coords]; simp
  have e3 : conjB x 3 = -x 3 := by rw [conjB_coords]; simp
  have e4 : conjB x 4 = -x 4 := by rw [conjB_coords]; simp
  have e5 : conjB x 5 = x 5 := by rw [conjB_coords]; simp
  rw [e2, e3, e4, e5]
  constructor
  · rintro ⟨h2, h3⟩; constructor <;> linarith
  · rintro ⟨h2, h3⟩; constructor <;> linarith

/-- **DERIVED (§1.4).**  The image formulation of the same relation. -/
theorem conjB_maps_StabL :
    (∀ x ∈ StabL Hminus, conjB x ∈ StabL Hplus) ∧
    (∀ x ∈ StabL Hplus, conjB x ∈ StabL Hminus) := by
  refine ⟨fun x hx => (conjB_StabL_iff x).1 hx, fun x hx => ?_⟩
  rw [conjB_StabL_iff, conjB_conjB]
  exact hx

/-! ## §1.5, §1.6 — an explicit invariant subspace and reducibility -/

theorem Zspan_eminus_le_Hminus : Zspan eminus ≤ Hminus := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_Zspan_iff_central _ _).1 hy
  rw [Z_central hz eminus]
  exact mul_right_mem_SectorMinus
    ((mem_SectorMinus_iff_eminus _).2 eminus_selfProduct) z

/-- **PRINCIPAL THEOREM (§1.5, §1.6): `minus_sector_reducible`, `REDUCIBLE`.**  The plane
of central multiples of `e₋` is a proper nonzero subspace of the minus sector which is
invariant under every element of the exact left stabilizer of the minus sector.  Hence
`H₋` is reducible under the weakest structure that actually preserves it. -/
theorem Hminus_reducible :
    Zspan eminus ≤ Hminus ∧ Zspan eminus ≠ ⊥ ∧ Zspan eminus ≠ Hminus ∧
      ∀ x ∈ StabL Hminus, ∀ ψ ∈ Zspan eminus, x ⋆ ψ ∈ Zspan eminus := by
  have hdim2 : Module.finrank ℝ (Zspan eminus) = 2 := finrank_Zspan eminus_ne_zero
  refine ⟨Zspan_eminus_le_Hminus, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot] at hdim2
    simp at hdim2
  · intro heq
    rw [heq, finrank_SectorMinus] at hdim2
    norm_num at hdim2
  · intro x hx ψ hψ
    obtain ⟨z, hz, rfl⟩ := (mem_Zspan_iff_central _ _).1 hψ
    have hxe : x ⋆ eminus ∈ Zspan eminus := by
      have hker : eplus ⋆ (x ⋆ eminus) = 0 := by
        rw [StabL_Hminus_eq_ker] at hx
        exact hx
      have hsplit : (w1 : W) ⋆ (x ⋆ eminus) = (eminus + eplus) ⋆ (x ⋆ eminus) := by
        rw [add_comm, eplus_add_eminus]
      rw [one_mul_W, add_mul_W, hker, add_zero] at hsplit
      rw [hsplit]
      exact compress_mem_Zspan eminus_selfProduct eminus_ne_zero eminus_coord_0
        eminus_coord_7 x
    obtain ⟨z', hz', hz'e⟩ := (mem_Zspan_iff_central _ _).1 hxe
    refine (mem_Zspan_iff_central _ _).2 ⟨z' ⋆ z, Z_mul_mem hz' hz, ?_⟩
    calc (z' ⋆ z) ⋆ eminus = z' ⋆ (z ⋆ eminus) := mul_assoc_W _ _ _
      _ = z' ⋆ (eminus ⋆ z) := by rw [Z_central hz eminus]
      _ = (z' ⋆ eminus) ⋆ z := (mul_assoc_W _ _ _).symm
      _ = (x ⋆ eminus) ⋆ z := by rw [hz'e]
      _ = x ⋆ (eminus ⋆ z) := mul_assoc_W _ _ _
      _ = x ⋆ (z ⋆ eminus) := by rw [Z_central hz eminus]

/-- **§1 SUMMARY, DERIVED, AXIS-RELATIVE.**  The complete minus-sector hardening report:
exact stabilizer as a kernel, exact dimension six, subalgebra, exact coordinate
characterization, exact structural relation with the plus stabilizer, and reducibility
with an explicit proper nonzero invariant subspace. -/
theorem minus_sector_hardening_report :
    StabL Hminus = LinearMap.ker crossMP ∧
    Module.finrank ℝ (StabL Hminus) = 6 ∧
    (∀ x ∈ StabL Hminus, ∀ y ∈ StabL Hminus, x ⋆ y ∈ StabL Hminus) ∧
    (∀ x : W, x ∈ StabL Hminus ↔ x 2 + x 4 = 0 ∧ x 3 + x 5 = 0) ∧
    (∀ x : W, x ∈ StabL Hminus ↔ conjB x ∈ StabL Hplus) ∧
    (Zspan eminus ≤ Hminus ∧ Zspan eminus ≠ ⊥ ∧ Zspan eminus ≠ Hminus ∧
      ∀ x ∈ StabL Hminus, ∀ ψ ∈ Zspan eminus, x ⋆ ψ ∈ Zspan eminus) :=
  ⟨StabL_Hminus_eq_ker, finrank_StabL_Hminus, StabL_Hminus_algebra.2.2.2.2,
    mem_StabL_Hminus_iff_coords, conjB_StabL_iff, Hminus_reducible⟩

end NullSectorTask13
