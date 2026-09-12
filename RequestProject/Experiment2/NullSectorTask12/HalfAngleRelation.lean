import RequestProject.Experiment2.NullSectorTask12.AxisRelation
import RequestProject.Experiment2.NullSectorTask10.HalfAngleSectors

/-!
# Task 12, Layer 7: relation to the inherited half-angle sectors (§21, §22, §23)

**Source order (§39).**  The intrinsic classification of left carriers is complete before
this module: the half-angle sectors of Task 10 are imported here for the first time, and
they are *tested*, never used to produce carriers.

## Results

* `H₊` and `H₋` are **not** left carriers: left multiplication by a transverse basis
  element leaves them (§22).  What they are is the exact opposite: each of them is the
  set of left multiples of the algebra by a fixed self-product element, i.e. a *right*
  ideal, closed under multiplication on the right by all of `W`.
* The exact set of elements whose left multiplication preserves `H₊` is a subalgebra of
  real dimension `6` — the kernel of the compression `x ↦ e₋ ⋆ x ⋆ e₊` — so the failure of
  left stability is a codimension-two phenomenon (§23).
* Under that exact stabilizer `H₊` is **REDUCIBLE**: the two-dimensional plane of central
  multiples of `e₊` is a proper nonzero invariant subspace (§23).
* For *every* minimal left carrier `L` (no matter where it sits in the family):
  `dimℝ (L ⊓ H₊) = dimℝ (L ⊓ H₋) = 2` and `L = (L ⊓ H₊) ⊕ (L ⊓ H₋)` (§21).  In
  particular no minimal carrier is contained in either sector.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## The two axial self-product elements -/

/-- The axial self-product element of the plus sector. -/
noncomputable def eplus : W := esph 1 0 0

/-- The axial self-product element of the minus sector. -/
noncomputable def eminus : W := esph (-1) 0 0

theorem eplus_eq : eplus = (2⁻¹ : ℝ) • (w1 + wA) := by
  funext i; fin_cases i <;> norm_num [eplus, esph, w1, wA]

theorem eminus_eq : eminus = (2⁻¹ : ℝ) • (w1 - wA) := by
  funext i; fin_cases i <;> norm_num [eminus, esph, w1, wA]

theorem eplus_selfProduct : IsSelfProduct eplus := esph_selfProduct (by norm_num)

theorem eminus_selfProduct : IsSelfProduct eminus := esph_selfProduct (by norm_num)

theorem eplus_ne_zero : eplus ≠ 0 := esph_ne_zero 1 0 0

theorem eminus_ne_zero : eminus ≠ 0 := esph_ne_zero (-1) 0 0

@[simp] theorem eplus_coord_0 : eplus 0 = 1 / 2 := rfl
@[simp] theorem eplus_coord_7 : eplus 7 = 0 := rfl
@[simp] theorem eminus_coord_0 : eminus 0 = 1 / 2 := rfl
@[simp] theorem eminus_coord_7 : eminus 7 = 0 := rfl

theorem eplus_add_eminus : eplus + eminus = w1 := by
  funext i; fin_cases i <;> norm_num [eplus, eminus, esph, w1]

theorem eminus_eq_sub : eminus = w1 - eplus := by
  rw [← eplus_add_eminus]; abel

theorem eplus_mul (ψ : W) : eplus ⋆ ψ = (2⁻¹ : ℝ) • (ψ + wA ⋆ ψ) := by
  rw [eplus_eq, smul_mul_W, add_mul_W, one_mul_W]

theorem eminus_mul (ψ : W) : eminus ⋆ ψ = (2⁻¹ : ℝ) • (ψ - wA ⋆ ψ) := by
  rw [eminus_eq, smul_mul_W, sub_eq_add_neg, add_mul_W, one_mul_W, neg_mul_W,
    ← sub_eq_add_neg]

/-! ## The sectors are exactly the left multiples of the two axial elements -/

theorem mem_SectorPlus_iff_eplus (ψ : W) : ψ ∈ SectorPlus ↔ eplus ⋆ ψ = ψ := by
  rw [mem_SectorPlus_iff_axis, eplus_mul]
  constructor
  · intro h; rw [h]; module
  · intro h
    have h2 : ψ + wA ⋆ ψ = (2 : ℝ) • ψ := by
      have h3 := congrArg (fun y : W => (2 : ℝ) • y) h
      simp only [smul_smul] at h3
      norm_num at h3
      exact h3
    have h4 : wA ⋆ ψ = (2 : ℝ) • ψ - ψ := by rw [← h2]; abel
    rw [h4]; module

theorem mem_SectorMinus_iff_eminus (ψ : W) : ψ ∈ SectorMinus ↔ eminus ⋆ ψ = ψ := by
  rw [mem_SectorMinus_iff_axis, eminus_mul]
  constructor
  · intro h; rw [h]; module
  · intro h
    have h2 : ψ - wA ⋆ ψ = (2 : ℝ) • ψ := by
      have h3 := congrArg (fun y : W => (2 : ℝ) • y) h
      simp only [smul_smul] at h3
      norm_num at h3
      exact h3
    have h4 : wA ⋆ ψ = ψ - (2 : ℝ) • ψ := by rw [← h2]; abel
    rw [h4]; module

/-- **DERIVED (§22).**  The plus sector is exactly the set of left multiples of the
algebra by the axial element: a *right* ideal, not a left one. -/
theorem SectorPlus_eq_range : SectorPlus = LinearMap.range (Lmul eplus) := by
  ext ψ
  simp only [LinearMap.mem_range, Lmul_apply]
  constructor
  · intro h; exact ⟨ψ, (mem_SectorPlus_iff_eplus ψ).1 h⟩
  · rintro ⟨x, rfl⟩
    rw [mem_SectorPlus_iff_eplus, ← mul_assoc_W, eplus_selfProduct]

theorem SectorMinus_eq_range : SectorMinus = LinearMap.range (Lmul eminus) := by
  ext ψ
  simp only [LinearMap.mem_range, Lmul_apply]
  constructor
  · intro h; exact ⟨ψ, (mem_SectorMinus_iff_eminus ψ).1 h⟩
  · rintro ⟨x, rfl⟩
    rw [mem_SectorMinus_iff_eminus, ← mul_assoc_W, eminus_selfProduct]

/-- **DERIVED (§22).**  The sectors are stable under multiplication on the *right* by
every algebra element. -/
theorem mul_right_mem_SectorPlus {ψ : W} (hψ : ψ ∈ SectorPlus) (x : W) :
    ψ ⋆ x ∈ SectorPlus := by
  rw [mem_SectorPlus_iff_eplus] at hψ ⊢
  rw [← mul_assoc_W, hψ]

theorem mul_right_mem_SectorMinus {ψ : W} (hψ : ψ ∈ SectorMinus) (x : W) :
    ψ ⋆ x ∈ SectorMinus := by
  rw [mem_SectorMinus_iff_eminus] at hψ ⊢
  rw [← mul_assoc_W, hψ]

/-! ## §22 — the sectors are not left carriers -/

/-- **PRINCIPAL NEGATIVE RESULT (§22).**  The plus sector is *not* stable under left
multiplication by the whole algebra. -/
theorem not_isLeftCarrier_SectorPlus : ¬ IsLeftCarrier SectorPlus := by
  intro h
  have hmem : eplus ∈ SectorPlus := by
    rw [mem_SectorPlus_iff_eplus]; exact eplus_selfProduct
  have hBmem := h wB eplus hmem
  rw [mem_SectorPlus_iff_axis] at hBmem
  have h2 := congrArg (fun y : W => y 2) hBmem
  simp [eplus, esph, wA, wB, wit8MulFun] at h2
  norm_num at h2

/-- **PRINCIPAL NEGATIVE RESULT (§22).**  The minus sector is not a left carrier
either. -/
theorem not_isLeftCarrier_SectorMinus : ¬ IsLeftCarrier SectorMinus := by
  intro h
  have hmem : eminus ∈ SectorMinus := by
    rw [mem_SectorMinus_iff_eminus]; exact eminus_selfProduct
  have hBmem := h wB eminus hmem
  rw [mem_SectorMinus_iff_axis] at hBmem
  have h2 := congrArg (fun y : W => y 2) hBmem
  simp [eminus, esph, wA, wB, wit8MulFun] at h2
  norm_num at h2

/-! ## §23 — the exact left stabilizer of the plus sector -/

/-- The exact set of algebra elements whose left multiplication preserves a subspace. -/
def StabL (L : Submodule ℝ W) : Submodule ℝ W where
  carrier := {x : W | ∀ ψ ∈ L, x ⋆ ψ ∈ L}
  zero_mem' := by intro ψ _; rw [zero_mul_W]; exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb ψ hψ
    rw [add_mul_W]
    exact Submodule.add_mem _ (ha ψ hψ) (hb ψ hψ)
  smul_mem' := by
    intro c a ha ψ hψ
    rw [smul_mul_W]
    exact Submodule.smul_mem _ c (ha ψ hψ)

theorem mem_StabL_iff (L : Submodule ℝ W) (x : W) :
    x ∈ StabL L ↔ ∀ ψ ∈ L, x ⋆ ψ ∈ L := Iff.rfl

/-- The compression operator that measures the failure of left stability. -/
noncomputable def crossPM : W →ₗ[ℝ] W := (Lmul eminus).comp (Rmul eplus)

@[simp] theorem crossPM_apply (x : W) : crossPM x = eminus ⋆ (x ⋆ eplus) := rfl

theorem crossPM_idem (x : W) : crossPM (crossPM x) = crossPM x := by
  simp only [crossPM_apply]
  rw [mul_assoc_W eminus (x ⋆ eplus) eplus, mul_assoc_W x eplus eplus, eplus_selfProduct,
    ← mul_assoc_W eminus eminus (x ⋆ eplus), eminus_selfProduct]

theorem finrank_range_crossPM : Module.finrank ℝ (LinearMap.range crossPM) = 2 := by
  have h := finrank_range_of_idem crossPM_idem
  rw [crossPM, trace_Lmul_comp_Rmul, eminus_coord_0, eminus_coord_7, eplus_coord_0,
    eplus_coord_7] at h
  have h2 : ((Module.finrank ℝ (LinearMap.range crossPM) : ℝ)) = ((2 : ℕ) : ℝ) := by
    rw [crossPM]; rw [h]; norm_num
  exact_mod_cast h2

/-- **DERIVED (§23).**  The exact left stabilizer of the plus sector is the kernel of the
compression `x ↦ e₋ ⋆ x ⋆ e₊`. -/
theorem StabL_SectorPlus_eq_ker : StabL SectorPlus = LinearMap.ker crossPM := by
  ext x
  simp only [mem_StabL_iff, LinearMap.mem_ker, crossPM_apply]
  constructor
  · intro hx
    have hmem : eplus ∈ SectorPlus := by
      rw [mem_SectorPlus_iff_eplus]; exact eplus_selfProduct
    have h1 := (mem_SectorPlus_iff_eplus _).1 (hx eplus hmem)
    have : eminus ⋆ (x ⋆ eplus) = (w1 - eplus) ⋆ (x ⋆ eplus) := by rw [← eminus_eq_sub]
    rw [this, sub_eq_add_neg, add_mul_W, one_mul_W, neg_mul_W, h1]
    abel
  · intro hx ψ hψ
    obtain ⟨y, rfl⟩ : ∃ y : W, eplus ⋆ y = ψ := by
      rw [SectorPlus_eq_range] at hψ; exact hψ
    have hxe : eplus ⋆ (x ⋆ eplus) = x ⋆ eplus := by
      have hsplit : (w1 : W) ⋆ (x ⋆ eplus) = (eplus + eminus) ⋆ (x ⋆ eplus) := by
        rw [eplus_add_eminus]
      rw [one_mul_W, add_mul_W, hx, add_zero] at hsplit
      exact hsplit.symm
    have hmem : x ⋆ eplus ∈ SectorPlus := (mem_SectorPlus_iff_eplus _).2 hxe
    have := mul_right_mem_SectorPlus hmem y
    rwa [mul_assoc_W] at this

/-- **PRINCIPAL THEOREM (§23).**  The exact left stabilizer of the plus sector has real
dimension six: left stability fails in exactly two dimensions. -/
theorem finrank_StabL_SectorPlus : Module.finrank ℝ (StabL SectorPlus) = 6 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker crossPM
  rw [finrank_range_crossPM, ← StabL_SectorPlus_eq_ker] at hrk
  have h8 : Module.finrank ℝ W = 8 := finrank_W
  omega

/-- The exact left stabilizer is closed under multiplication and contains the unit, the
central plane and the distinguished axis, but not a transverse basis element. -/
theorem StabL_SectorPlus_algebra :
    w1 ∈ StabL SectorPlus ∧ wS ∈ StabL SectorPlus ∧ wA ∈ StabL SectorPlus ∧
      wB ∉ StabL SectorPlus ∧
      ∀ x ∈ StabL SectorPlus, ∀ y ∈ StabL SectorPlus, x ⋆ y ∈ StabL SectorPlus := by
  refine ⟨fun ψ hψ => by rwa [one_mul_W], fun ψ hψ => wS_mul_mem_SectorPlus hψ, ?_, ?_, ?_⟩
  · intro ψ hψ
    rw [mem_SectorPlus_iff_axis] at hψ
    rw [hψ]
    exact (mem_SectorPlus_iff_axis ψ).2 hψ
  · intro hB
    have hmem : eplus ∈ SectorPlus := by
      rw [mem_SectorPlus_iff_eplus]; exact eplus_selfProduct
    have hBmem := hB eplus hmem
    rw [mem_SectorPlus_iff_axis] at hBmem
    have h2 := congrArg (fun y : W => y 2) hBmem
    simp [eplus, esph, wA, wB, wit8MulFun] at h2
    norm_num at h2
  · intro x hx y hy ψ hψ
    rw [mul_assoc_W]
    exact hx _ (hy ψ hψ)

/-! ## §23 — the plus sector is reducible under its exact stabilizer -/

theorem mem_Zspan_iff_central (e y : W) : y ∈ Zspan e ↔ ∃ z ∈ Z, z ⋆ e = y := by
  rw [mem_Zspan_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a • w1 + b • wS, smul_add_smul_mem_Z a b, zsmul_mul a b e⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 hz
    exact ⟨a, b, (zsmul_mul a b e).symm⟩

theorem Zspan_eplus_le_SectorPlus : Zspan eplus ≤ SectorPlus := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_Zspan_iff_central _ _).1 hy
  rw [Z_central hz eplus]
  exact mul_right_mem_SectorPlus
    ((mem_SectorPlus_iff_eplus _).2 eplus_selfProduct) z

/-- **PRINCIPAL THEOREM (§23): `REDUCIBLE`.**  The plane of central multiples of `e₊` is a
proper nonzero subspace of the plus sector which is invariant under every element of the
exact left stabilizer.  Hence the plus sector is reducible under the weakest structure it
actually preserves. -/
theorem SectorPlus_reducible :
    Zspan eplus ≤ SectorPlus ∧ Zspan eplus ≠ ⊥ ∧ Zspan eplus ≠ SectorPlus ∧
      ∀ x ∈ StabL SectorPlus, ∀ ψ ∈ Zspan eplus, x ⋆ ψ ∈ Zspan eplus := by
  have hdim2 : Module.finrank ℝ (Zspan eplus) = 2 := finrank_Zspan eplus_ne_zero
  refine ⟨Zspan_eplus_le_SectorPlus, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot] at hdim2
    simp at hdim2
  · intro heq
    rw [heq, finrank_SectorPlus] at hdim2
    norm_num at hdim2
  · intro x hx ψ hψ
    obtain ⟨z, hz, rfl⟩ := (mem_Zspan_iff_central _ _).1 hψ
    have hxe : x ⋆ eplus ∈ Zspan eplus := by
      have hker : eminus ⋆ (x ⋆ eplus) = 0 := by
        rw [StabL_SectorPlus_eq_ker] at hx
        exact hx
      have hsplit : (w1 : W) ⋆ (x ⋆ eplus) = (eplus + eminus) ⋆ (x ⋆ eplus) := by
        rw [eplus_add_eminus]
      rw [one_mul_W, add_mul_W, hker, add_zero] at hsplit
      rw [hsplit]
      exact compress_mem_Zspan eplus_selfProduct eplus_ne_zero eplus_coord_0
        eplus_coord_7 x
    obtain ⟨z', hz', hz'e⟩ := (mem_Zspan_iff_central _ _).1 hxe
    refine (mem_Zspan_iff_central _ _).2 ⟨z' ⋆ z, Z_mul_mem hz' hz, ?_⟩
    calc (z' ⋆ z) ⋆ eplus = z' ⋆ (z ⋆ eplus) := mul_assoc_W _ _ _
      _ = z' ⋆ (eplus ⋆ z) := by rw [Z_central hz eplus]
      _ = (z' ⋆ eplus) ⋆ z := (mul_assoc_W _ _ _).symm
      _ = (x ⋆ eplus) ⋆ z := by rw [hz'e]
      _ = x ⋆ (eplus ⋆ z) := mul_assoc_W _ _ _
      _ = x ⋆ (z ⋆ eplus) := by rw [Z_central hz eplus]

/-! ## §21 — the intersections of a minimal carrier with the two sectors -/

/-- The compression of a minimal carrier into the plus sector. -/
noncomputable def sectorCompress (s e : W) : W →ₗ[ℝ] W := (Lmul s).comp (Rmul e)

@[simp] theorem sectorCompress_apply (s e x : W) : sectorCompress s e x = s ⋆ (x ⋆ e) :=
  rfl

theorem sectorCompress_idem {s e : W} (hs : IsSelfProduct s) (he : IsSelfProduct e)
    (x : W) : sectorCompress s e (sectorCompress s e x) = sectorCompress s e x := by
  simp only [sectorCompress_apply]
  rw [mul_assoc_W s (x ⋆ e) e, mul_assoc_W x e e, he, ← mul_assoc_W s s (x ⋆ e), hs]

theorem finrank_range_sectorCompress {s e : W} (hs : IsSelfProduct s)
    (he : IsSelfProduct e) (hs0 : s 0 = 1 / 2) (hs7 : s 7 = 0) (he0 : e 0 = 1 / 2)
    (he7 : e 7 = 0) : Module.finrank ℝ (LinearMap.range (sectorCompress s e)) = 2 := by
  have h := finrank_range_of_idem (sectorCompress_idem hs he)
  rw [sectorCompress, trace_Lmul_comp_Rmul, hs0, hs7, he0, he7] at h
  have h2 : ((Module.finrank ℝ (LinearMap.range (sectorCompress s e)) : ℝ))
      = ((2 : ℕ) : ℝ) := by
    rw [sectorCompress]; rw [h]; norm_num
  exact_mod_cast h2

theorem range_sectorCompress_eq_inf (e : W) :
    LinearMap.range (sectorCompress eplus e) = Lgen e ⊓ SectorPlus := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_inf, mem_Lgen_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨eplus ⋆ x, mul_assoc_W eplus x e⟩, ?_⟩
    show eplus ⋆ (x ⋆ e) ∈ SectorPlus
    rw [mem_SectorPlus_iff_eplus, ← mul_assoc_W, eplus_selfProduct]
  · rintro ⟨⟨x, rfl⟩, hplus⟩
    exact ⟨x, (mem_SectorPlus_iff_eplus _).1 hplus⟩

theorem range_sectorCompress_eq_inf_minus (e : W) :
    LinearMap.range (sectorCompress eminus e) = Lgen e ⊓ SectorMinus := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_inf, mem_Lgen_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨eminus ⋆ x, mul_assoc_W eminus x e⟩, ?_⟩
    show eminus ⋆ (x ⋆ e) ∈ SectorMinus
    rw [mem_SectorMinus_iff_eminus, ← mul_assoc_W, eminus_selfProduct]
  · rintro ⟨⟨x, rfl⟩, hminus⟩
    exact ⟨x, (mem_SectorMinus_iff_eminus _).1 hminus⟩

/-- **PRINCIPAL THEOREM (§21).**  Every minimal left carrier meets each half-angle sector
in exactly two real dimensions, and is the direct sum of the two intersections.  No
minimal carrier lies inside a sector. -/
theorem minimal_inf_sectors {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    Module.finrank ℝ (L ⊓ SectorPlus : Submodule ℝ W) = 2 ∧
    Module.finrank ℝ (L ⊓ SectorMinus : Submodule ℝ W) = 2 ∧
    (L ⊓ SectorPlus) ⊔ (L ⊓ SectorMinus) = L ∧
    (L ⊓ SectorPlus) ⊓ (L ⊓ SectorMinus) = ⊥ := by
  obtain ⟨e, he, hne, -, he0, he7, rfl⟩ := isMinimal_eq_Lgen_selfProduct hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← range_sectorCompress_eq_inf e]
    exact finrank_range_sectorCompress eplus_selfProduct he eplus_coord_0 eplus_coord_7
      he0 he7
  · rw [← range_sectorCompress_eq_inf_minus e]
    exact finrank_range_sectorCompress eminus_selfProduct he eminus_coord_0
      eminus_coord_7 he0 he7
  · refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    intro ψ hψ
    have hsplit : ψ = eplus ⋆ ψ + eminus ⋆ ψ := by
      rw [← add_mul_W, eplus_add_eminus, one_mul_W]
    have hp : eplus ⋆ ψ ∈ (Lgen e ⊓ SectorPlus : Submodule ℝ W) :=
      Submodule.mem_inf.2 ⟨isLeftCarrier_Lgen e eplus ψ hψ, by
        rw [mem_SectorPlus_iff_eplus, ← mul_assoc_W, eplus_selfProduct]⟩
    have hm : eminus ⋆ ψ ∈ (Lgen e ⊓ SectorMinus : Submodule ℝ W) :=
      Submodule.mem_inf.2 ⟨isLeftCarrier_Lgen e eminus ψ hψ, by
        rw [mem_SectorMinus_iff_eminus, ← mul_assoc_W, eminus_selfProduct]⟩
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hm)
  · refine le_bot_iff.1 ?_
    intro ψ hψ
    have h1 : ψ ∈ SectorPlus := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hψ).1).2
    have h2 : ψ ∈ SectorMinus := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hψ).2).2
    have := SectorPlus_inf_SectorMinus
    rw [Submodule.eq_bot_iff] at this
    exact this ψ ⟨h1, h2⟩

end NullSectorTask12
