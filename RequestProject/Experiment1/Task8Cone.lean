import Mathlib
import RequestProject.Experiment1.Task8Intrinsic

/-!
# Task 8, Part B : the square cone as the primary cone

The primary cone of the intrinsic layer is

`𝒞_J = {H ∈ J : ∃ X ∈ J, H = X ∘ X}`.

Its definition (`Task8.ConeJ`) mentions only the carrier and the Jordan product: no
`PosSemidef`, no eigenvalues, no Minkowski coordinates and no Lorentz group.

Structural properties (B2) come first, then the intrinsic characterization by the intrinsic
trace and norm (B3), and only afterwards the standard identifications (B4) with the PSD cone
and with the coordinate future cone.
-/

noncomputable section

open Matrix Complex Herm2
open scoped ComplexOrder

namespace Task8

open Task7 (jH jordanL coe_jH SquareCone)

/-! ## B1 : the primary cone -/

/-- **B1 (primary definition).** The cone of Jordan squares of the carrier. -/
def ConeJ : Set Herm := {H : Herm | ∃ X : Herm, H = jH X X}

/-- Bridge to the Task-7 set-of-matrices version of the same cone. -/
theorem mem_coneJ_iff_coe_mem_squareCone (H : Herm) :
    H ∈ ConeJ ↔ ((H : M2)) ∈ SquareCone := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨(Matrix.isHermitian_iff_isSelfAdjoint).2 (jH X X).2, (X : M2),
      (Matrix.isHermitian_iff_isSelfAdjoint).2 X.2, rfl⟩
  · rintro ⟨-, K, hK, hHK⟩
    exact ⟨⟨K, (Matrix.isHermitian_iff_isSelfAdjoint).1 hK⟩, Subtype.ext hHK⟩

/-! ## B2 : structural properties -/

/-- **B2.1.** `0 ∈ 𝒞_J`. -/
theorem zero_mem_coneJ : (0 : Herm) ∈ ConeJ := by
  refine ⟨0, Subtype.ext ?_⟩
  show (0 : M2) = Carrier.jordan (0 : M2) (0 : M2)
  simp [Carrier.jordan]

/-- **B2.2.** `1 ∈ 𝒞_J`. -/
theorem one_mem_coneJ : Carrier.oneH ∈ ConeJ := by
  refine ⟨Carrier.oneH, Subtype.ext ?_⟩
  show (1 : M2) = Carrier.jordan (1 : M2) (1 : M2)
  simp [Carrier.jordan]
  module

/-- Real scalars act through their complex image. -/
theorem realSmul_eq (r : ℝ) (M : M2) : r • M = ((r : ℂ)) • M := by
  ext i j; simp [Complex.real_smul]

theorem jordan_smul_smul (a : ℝ) (A B : M2) :
    Carrier.jordan (a • A) (a • B) = (a * a) • Carrier.jordan A B := by
  simp only [Carrier.jordan, realSmul_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
  push_cast
  ring_nf

/-- The Jordan square of a rescaled element. -/
theorem jH_smul_self (a : ℝ) (X : Herm) : jH (a • X) (a • X) = (a * a) • jH X X :=
  Subtype.ext (jordan_smul_smul a (X : M2) (X : M2))

/-- **B2.3.** The cone is stable under nonnegative rescaling.  Purely Jordan-theoretic:
`r H = (√r X) ∘ (√r X)`. -/
theorem smul_mem_coneJ {H : Herm} (hH : H ∈ ConeJ) {r : ℝ} (hr : 0 ≤ r) : r • H ∈ ConeJ := by
  obtain ⟨X, rfl⟩ := hH
  refine ⟨Real.sqrt r • X, ?_⟩
  rw [jH_smul_self, ← Real.sqrt_mul_self hr]
  congr 1
  rw [Real.sqrt_mul_self hr, Real.mul_self_sqrt hr]

/-- **B2.4 (closure under addition).**  Proof aid (documented dependency): the ambient
positive-semidefinite machinery of the concrete model is used, through the Task-7 theorem
`squareCone_eq_psd`.  The *statement* is intrinsic. -/
theorem add_mem_coneJ {H K : Herm} (hH : H ∈ ConeJ) (hK : K ∈ ConeJ) : H + K ∈ ConeJ := by
  rw [mem_coneJ_iff_coe_mem_squareCone] at hH hK ⊢
  rw [Task7.squareCone_eq_psd] at hH hK ⊢
  exact Matrix.PosSemidef.add hH hK

/-- **B2.5 (pointedness).** `𝒞_J ∩ (-𝒞_J) = {0}`. -/
theorem coneJ_pointed {H : Herm} (h₁ : H ∈ ConeJ) (h₂ : -H ∈ ConeJ) : H = 0 := by
  rw [mem_coneJ_iff_coe_mem_squareCone] at h₁ h₂
  have h₂' : -((H : M2)) ∈ SquareCone := by simpa using h₂
  exact Subtype.ext (Task7.squareCone_pointed h₁ h₂')

/-- **B2.6.** `-1 ∉ 𝒞_J`: the cone is genuinely oriented by the Jordan data. -/
theorem neg_one_not_mem_coneJ : -Carrier.oneH ∉ ConeJ := by
  intro h
  rw [mem_coneJ_iff_coe_mem_squareCone] at h
  exact Task7.neg_one_not_mem_squareCone (by simpa using h)

/-! ## B3 : intrinsic characterization by the intrinsic trace and norm -/

/-- **B3.** `H ∈ 𝒞_J ↔ trJ H ≥ 0 ∧ N_intr H ≥ 0`.  Both sides of the equivalence use only
intrinsically defined data. -/
theorem mem_coneJ_iff (H : Herm) : H ∈ ConeJ ↔ 0 ≤ trJ H ∧ 0 ≤ Nintr H := by
  rw [mem_coneJ_iff_coe_mem_squareCone, Task7.squareCone_eq_psd]
  rw [show (((H : M2)) ∈ {H : M2 | H.PosSemidef}) ↔ ((H : M2)).PosSemidef from Iff.rfl]
  rw [Task7.psd_iff_trace_and_norm_nonneg H, trJ_eq_matrix_trace, Nintr_eq_NJr]

/-! ## B4 : standard identifications (`STANDARD_IDENTIFICATION`) -/

/-- **B4 (STANDARD_IDENTIFICATION).** The primary cone is the positive semidefinite cone. -/
theorem coneJ_eq_psd : ConeJ = {H : Herm | ((H : M2)).PosSemidef} := by
  ext H
  rw [mem_coneJ_iff_coe_mem_squareCone, Task7.squareCone_eq_psd]
  exact Iff.rfl

/-- **B4 (STANDARD_IDENTIFICATION).**  In the standard coordinates the primary cone is the
closed future cone `T ≥ 0 ∧ T² - X² - Y² - Z² ≥ 0`. -/
theorem mem_coneJ_coords (T X Y Z : ℝ) :
    hermCoordEquiv ![T, X, Y, Z] ∈ ConeJ ↔ 0 ≤ T ∧ 0 ≤ T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := by
  rw [mem_coneJ_iff, trJ_hermCoordEquiv, Nintr_hermCoordEquiv, Qform]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    simpa using h2
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    simpa using h2

end Task8
