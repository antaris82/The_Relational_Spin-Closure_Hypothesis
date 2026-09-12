import Mathlib

/-!
# Spine / E1 : the `2 × 2` complex matrix model

The intrinsic core needs a *faithful representation* of the real Clifford algebra `Cl₃(ℝ)`
in order to compare the intrinsic spin group with `SL(2,ℂ)`.  The target of that
representation is the associative algebra `M₂(ℂ)` together with the traceless Hermitian
matrix pattern `hMat T X Y Z = !![T+Z, X-iY; X+iY, T-Z]`.

This module supplies exactly that data, and nothing else:

* `SpinCore.M2` — the algebra `M₂(ℂ)`;
* `SpinCore.hMat` and its additivity / real homogeneity / Hermiticity;
* `SpinCore.hMat_sq` — the Clifford relation satisfied by the pattern with `T = 0`;
* `SpinCore.center_eq_complexScalars` — the centre of `M₂(ℂ)` is `ℂ · 1`.

**Import firewall.**  `Mathlib` only.  In particular the historical Hermitian *Jordan
carrier* layer (the real subspace `selfAdjoint M₂(ℂ)` with the Jordan product, its trace,
its intrinsic norm, its positivity cone and the associated automorphism groups) is **not**
imported: nothing here mentions `selfAdjoint`, a Jordan product or a cone.  The matrix
pattern is used as a *representation target* only.

**Provenance.**  The pattern `hMat` and its three elementary lemmas are the corresponding
declarations of the upstream experiment-1 module `Herm2`; `hMat_sq` replaces the upstream
route through the Jordan-product identity `Task7.hMat_jordan`, and
`center_eq_complexScalars` replaces the upstream route through the matrix-unit lemmas of
`Task6Complex`.  Both replacements are proved here directly from the entries.
-/

noncomputable section

open Matrix Complex

namespace SpinCore

/-- The ambient associative algebra `M₂(ℂ)`. -/
abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- `hMat T X Y Z = !![T + Z, X - iY; X + iY, T - Z]`. -/
def hMat (T X Y Z : ℝ) : M2 :=
  !![((T + Z : ℝ) : ℂ), (X : ℂ) - (Y : ℝ) * I; (X : ℝ) + (Y : ℝ) * I, ((T - Z : ℝ) : ℂ)]

@[simp] theorem hMat_00 (T X Y Z : ℝ) : hMat T X Y Z 0 0 = ((T + Z : ℝ) : ℂ) := rfl
@[simp] theorem hMat_01 (T X Y Z : ℝ) : hMat T X Y Z 0 1 = (X : ℂ) - (Y : ℝ) * I := rfl
@[simp] theorem hMat_10 (T X Y Z : ℝ) : hMat T X Y Z 1 0 = (X : ℂ) + (Y : ℝ) * I := rfl
@[simp] theorem hMat_11 (T X Y Z : ℝ) : hMat T X Y Z 1 1 = ((T - Z : ℝ) : ℂ) := rfl

/-- `hMat T X Y Z` is Hermitian. -/
theorem hMat_isHermitian (T X Y Z : ℝ) : (hMat T X Y Z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem hMat_add (T X Y Z T' X' Y' Z' : ℝ) :
    hMat (T + T') (X + X') (Y + Y') (Z + Z') = hMat T X Y Z + hMat T' X' Y' Z' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hMat, Complex.ext_iff] <;> ring

theorem hMat_smul (r T X Y Z : ℝ) :
    hMat (r * T) (r * X) (r * Y) (r * Z) = r • hMat T X Y Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Complex.ext_iff, Matrix.smul_apply, Complex.real_smul]; ring

/-- **The Clifford relation of the matrix pattern.**  A traceless pattern squares to the
scalar `X² + Y² + Z²`.  Proved directly from the entries; no Jordan product is used. -/
theorem hMat_sq (X Y Z : ℝ) :
    hMat 0 X Y Z * hMat 0 X Y Z = algebraMap ℝ M2 (X ^ 2 + Y ^ 2 + Z ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Matrix.mul_apply, Fin.sum_univ_succ, Algebra.algebraMap_eq_smul_one,
      Complex.ext_iff, -Complex.ofReal_pow] <;> refine ⟨?_, ?_⟩ <;> ring

/-- **The centre of `M₂(ℂ)`.**  A matrix commuting with every matrix is a complex scalar.
Proved directly, by commuting with the two off-diagonal matrix units. -/
theorem center_eq_complexScalars (C : M2) :
    (∀ X : M2, C * X = X * C) ↔ ∃ lam : ℂ, C = lam • (1 : M2) := by
  constructor
  · intro h
    refine ⟨C 0 0, ?_⟩
    have h1 := h !![0, 1; 0, 0]
    have h2 := h !![0, 0; 1, 0]
    have e00 := congrFun (congrFun h1 0) 1
    have e01 := congrFun (congrFun h2 0) 0
    have e10 := congrFun (congrFun h1 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at e00 e01 e10
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e01, e10]
  · rintro ⟨lam, rfl⟩ X
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

end SpinCore
