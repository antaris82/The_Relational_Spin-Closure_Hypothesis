import Mathlib
import RequestProject.Experiment1.Task6Jordan

/-!
# Task 7, Part A : can trace and determinant be reconstructed *before* Lorentz symmetry?

Everything in this file uses only

* the associative multiplication of `M₂(ℂ)` (equivalently its Jordan symmetrization),
* complex linearity,
* the unit,

and **never** the Lorentz group, the determinant-preserving group, or any group defined by
determinant preservation.  The anti-circularity audit for these statements is therefore
immediate: no declaration below mentions `SO⁺(1,3)`, `G_det`, `DetConeAut` or the congruence
action.

## Contents

* `A1`  existence and uniqueness of the Cayley–Hamilton quadratic coefficient `N_J`,
  and `N_J = det`;
* a negative companion result: the *pair* `(t, n)` in `H² - tH + nI = 0` is **not** unique
  for scalar `H`, so the trace coefficient cannot be characterized by Cayley–Hamilton alone;
* `A2`  the trace-only formula `det H = ((tr H)² - tr (H²))/2`;
* `A3`  an intrinsic uniqueness theorem for the trace: a ℂ-linear functional with
  `τ(XY) = τ(YX)` is a scalar multiple of `tr`, hence `τ(1) = 2` forces `τ = tr`;
  the trace of the regular representation is `2 tr`, so the trace is *derived* from the
  associative multiplication;
* a counterexample showing that ℂ-linearity cannot be weakened to ℝ-linearity.
-/

noncomputable section

open Matrix Complex

namespace Task7

/-- The ambient algebra, as fixed in the earlier tasks. -/
abbrev M2 : Type := Carrier.M2

/-! ## A1 : the Cayley–Hamilton quadratic coefficient -/

/-- **A1 (existence).** For every `H` there is a scalar `n` with `H² - (tr H)H + n I = 0`.

Honesty tag: the witness produced here is the matrix determinant, so this is an
*existence via the determinant*; it is upgraded to a genuine characterization by
`NJ_unique` and `NJ_eq_det` below, and to a determinant-free formula by `det_eq_trace_formula`. -/
theorem exists_NJ (H : M2) :
    ∃ n : ℂ, H * H - (Matrix.trace H) • H + n • (1 : M2) = 0 :=
  ⟨H.det, Carrier.cayleyHamilton_two H⟩

/-- **A1 (uniqueness).** The quadratic coefficient is unique.  The proof uses only that
`I ≠ 0`; no Lorentz symmetry, no group, and no determinant. -/
theorem NJ_unique {H : M2} {n₁ n₂ : ℂ}
    (h₁ : H * H - (Matrix.trace H) • H + n₁ • (1 : M2) = 0)
    (h₂ : H * H - (Matrix.trace H) • H + n₂ • (1 : M2) = 0) : n₁ = n₂ := by
  have h : (n₁ - n₂) • (1 : M2) = 0 := by
    rw [sub_smul]
    linear_combination (norm := module) h₁ - h₂
  have h0 : (n₁ - n₂) = ((n₁ - n₂) • (1 : M2)) 0 0 := by simp
  rw [h] at h0
  simp at h0
  exact sub_eq_zero.mp h0

/-- **A1 (identification).** The unique quadratic coefficient is the determinant. -/
theorem NJ_eq_det {H : M2} {n : ℂ}
    (h : H * H - (Matrix.trace H) • H + n • (1 : M2) = 0) : n = H.det :=
  NJ_unique h (Carrier.cayleyHamilton_two H)

/-- **A1.** Packaged: `∃! n, H² - (tr H) H + n I = 0`, and that `n` is `det H`. -/
theorem existsUnique_NJ (H : M2) :
    ∃! n : ℂ, H * H - (Matrix.trace H) • H + n • (1 : M2) = 0 := by
  refine ⟨H.det, Carrier.cayleyHamilton_two H, ?_⟩
  intro n hn
  exact NJ_eq_det hn

/-- The Jordan form of the same statement: on `M₂(ℂ)` the Jordan square is the square,
so `N_J` is definable from the Jordan product and the trace alone. -/
theorem jordan_sq (H : M2) : Carrier.jordan H H = H * H := by
  unfold Carrier.jordan
  have : H * H + H * H = (2 : ℂ) • (H * H) := by module
  rw [this, smul_smul]
  norm_num

/-- **A1, Jordan version.** `H ∘ H - (tr H) H + (det H) I = 0`. -/
theorem jordan_cayleyHamilton (H : M2) :
    Carrier.jordan H H - (Matrix.trace H) • H + (H.det) • (1 : M2) = 0 := by
  rw [jordan_sq]; exact Carrier.cayleyHamilton_two H

/-- **Negative companion result (A1).**  Cayley–Hamilton alone does *not* single out the
linear coefficient: for a scalar matrix `λ I` every `t` occurs, with `n = tλ - λ²`.
Hence the trace really is extra data at this point, and must be obtained separately
(see `A3`). -/
theorem trace_coefficient_not_unique_on_scalars (lam t : ℂ) :
    (lam • (1 : M2)) * (lam • (1 : M2)) - t • (lam • (1 : M2))
      + (t * lam - lam ^ 2) • (1 : M2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> ring

/-! ## A2 : the trace-only formula for the determinant -/

/-- **A2.** `det H = ((tr H)² - tr (H²))/2` for every `2 × 2` complex matrix.

The right-hand side uses exactly two pieces of data: the associative product (to form `H²`,
equivalently the Jordan square `H ∘ H`) and the trace.  No determinant, no order, no group. -/
theorem det_eq_trace_formula (H : M2) :
    H.det = ((Matrix.trace H) ^ 2 - Matrix.trace (H * H)) / 2 := by
  simp [Matrix.det_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- **A2, Jordan version.** The same formula with the Jordan square. -/
theorem det_eq_trace_formula_jordan (H : M2) :
    H.det = ((Matrix.trace H) ^ 2 - Matrix.trace (Carrier.jordan H H)) / 2 := by
  rw [jordan_sq]; exact det_eq_trace_formula H

/-! ## A3 : is the trace itself canonical? -/

/-- The four matrix units, written concretely. -/
private def E00 : M2 := !![1, 0; 0, 0]
private def E01 : M2 := !![0, 1; 0, 0]
private def E10 : M2 := !![0, 0; 1, 0]
private def E11 : M2 := !![0, 0; 0, 1]

private theorem E00_mul_E01 : E00 * E01 = E01 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem E01_mul_E00 : E01 * E00 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem E11_mul_E10 : E11 * E10 = E10 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E11, E10, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem E10_mul_E11 : E10 * E11 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E11, E10, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem E01_mul_E10 : E01 * E10 = E00 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E00, E01, E10, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem E10_mul_E01 : E10 * E01 = E11 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E11, E01, E10, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem one_decomp : (1 : M2) = E00 + E11 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E00, E11, Matrix.one_apply]

private theorem matrix_decomp (X : M2) :
    X = (X 0 0) • E00 + (X 0 1) • E01 + (X 1 0) • E10 + (X 1 1) • E11 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E00, E01, E10, E11]

/-- **A3 (intrinsic characterization of the trace).**  Any ℂ-linear functional on `M₂(ℂ)`
that is symmetric under cyclic permutation is a scalar multiple of the trace, the scalar
being `τ(1)/2`.

No determinant, no order, no group, no `*`-structure is used. -/
theorem trace_unique_up_to_scale (tau : M2 →ₗ[ℂ] ℂ)
    (hcyc : ∀ X Y : M2, tau (X * Y) = tau (Y * X)) (X : M2) :
    tau X = (tau 1 / 2) * Matrix.trace X := by
  have h01 : tau E01 = 0 := by
    have := hcyc E00 E01
    rw [E00_mul_E01, E01_mul_E00] at this
    simpa using this
  have h10 : tau E10 = 0 := by
    have := hcyc E11 E10
    rw [E11_mul_E10, E10_mul_E11] at this
    simpa using this
  have hdiag : tau E00 = tau E11 := by
    have := hcyc E01 E10
    rw [E01_mul_E10, E10_mul_E01] at this
    exact this
  have hone : tau 1 = 2 * tau E00 := by
    rw [one_decomp, map_add, hdiag]
    ring
  have hX := congrArg tau (matrix_decomp X)
  simp only [map_add, map_smul, smul_eq_mul, h01, h10, mul_zero, add_zero] at hX
  have htr : Matrix.trace X = X 0 0 + X 1 1 := by
    simp [Matrix.trace, Fin.sum_univ_succ]
  rw [hX, hone, ← hdiag, htr]
  ring

/-- **A3 (normalized form).**  `τ(1) = 2` together with cyclicity and ℂ-linearity forces
`τ = tr`. -/
theorem trace_unique_of_normalized (tau : M2 →ₗ[ℂ] ℂ)
    (hone : tau 1 = 2) (hcyc : ∀ X Y : M2, tau (X * Y) = tau (Y * X)) (X : M2) :
    tau X = Matrix.trace X := by
  rw [trace_unique_up_to_scale tau hcyc X, hone]
  norm_num

/-- The trace of the left regular representation, as a ℂ-linear functional. -/
def regTraceL : M2 →ₗ[ℂ] ℂ := (LinearMap.trace ℂ M2) ∘ₗ (LinearMap.mul ℂ M2)

@[simp] theorem regTraceL_apply (X : M2) :
    regTraceL X = LinearMap.trace ℂ M2 (LinearMap.mulLeft ℂ X) := rfl

theorem finrank_M2 : Module.finrank ℂ M2 = 4 := by
  simp [M2, Carrier.M2, Herm2.M2, Module.finrank_matrix]

/-- **A3 (trace is derived).**  The trace of left multiplication by `X` on `M₂(ℂ)` is
`2 · tr X`.  Consequently the matrix trace *is* recovered, up to the canonical normalization
`τ(1) = dim = 4`, from the associative multiplication alone via the regular representation. -/
theorem regTraceL_eq (X : M2) : regTraceL X = 2 * Matrix.trace X := by
  have hcyc : ∀ X Y : M2, regTraceL (X * Y) = regTraceL (Y * X) := by
    intro X Y
    have hXY : LinearMap.mulLeft ℂ (X * Y)
        = LinearMap.mulLeft ℂ X * LinearMap.mulLeft ℂ Y := by
      ext z; simp
    have hYX : LinearMap.mulLeft ℂ (Y * X)
        = LinearMap.mulLeft ℂ Y * LinearMap.mulLeft ℂ X := by
      ext z; simp
    simp only [regTraceL_apply, hXY, hYX]
    exact LinearMap.trace_mul_comm ℂ _ _
  have hone : regTraceL 1 = 4 := by
    simp only [regTraceL_apply, LinearMap.mulLeft_one, LinearMap.trace_id]
    rw [finrank_M2]
    norm_num
  rw [trace_unique_up_to_scale regTraceL hcyc X, hone]
  norm_num

/-- The trace of the right regular representation is the same functional. -/
def regTraceR : M2 →ₗ[ℂ] ℂ := (LinearMap.trace ℂ M2) ∘ₗ (LinearMap.mul ℂ M2).flip

@[simp] theorem regTraceR_apply (X : M2) :
    regTraceR X = LinearMap.trace ℂ M2 (LinearMap.mulRight ℂ X) := rfl

theorem regTraceR_eq (X : M2) : regTraceR X = 2 * Matrix.trace X := by
  have hcyc : ∀ X Y : M2, regTraceR (X * Y) = regTraceR (Y * X) := by
    intro X Y
    have hXY : LinearMap.mulRight ℂ (X * Y)
        = LinearMap.mulRight ℂ Y * LinearMap.mulRight ℂ X := by
      ext z; simp
    have hYX : LinearMap.mulRight ℂ (Y * X)
        = LinearMap.mulRight ℂ X * LinearMap.mulRight ℂ Y := by
      ext z; simp
    simp only [regTraceR_apply, hXY, hYX]
    exact LinearMap.trace_mul_comm ℂ _ _
  have hone : regTraceR 1 = 4 := by
    simp only [regTraceR_apply, LinearMap.mulRight_one, LinearMap.trace_id]
    rw [finrank_M2]
    norm_num
  rw [trace_unique_up_to_scale regTraceR hcyc X, hone]
  norm_num

/-- **Determinant from the multiplication alone.**  Combining `A2` with `A3`, the
determinant of a `2 × 2` matrix is a polynomial expression in traces of regular
representations, i.e. in the associative multiplication and finite-dimensional linear
algebra only. -/
theorem det_from_regular_representation (H : M2) :
    H.det = ((regTraceL H / 2) ^ 2 - regTraceL (H * H) / 2) / 2 := by
  rw [regTraceL_eq, regTraceL_eq, det_eq_trace_formula]
  ring

/-! ### A3, negative part : complex linearity cannot be weakened -/

/-- The conjugated trace, as a **real**-linear functional on `M₂(ℂ)`. -/
def conjTrace : M2 →ₗ[ℝ] ℂ where
  toFun X := starRingEnd ℂ (Matrix.trace X)
  map_add' X Y := by simp
  map_smul' c X := by
    simp [Matrix.trace_smul, Complex.real_smul]

@[simp] theorem conjTrace_apply (X : M2) :
    conjTrace X = starRingEnd ℂ (Matrix.trace X) := rfl

/-- **A3 (counterexample).**  The conjugated trace is ℝ-linear, cyclic and normalized, but
is not the trace.  Hence in the uniqueness theorem `trace_unique_of_normalized` complex
linearity is genuinely needed: real linearity plus `τ(1) = 2` plus `τ(XY) = τ(YX)` does
**not** determine `τ`. -/
theorem conjTrace_counterexample :
    conjTrace 1 = 2 ∧ (∀ X Y : M2, conjTrace (X * Y) = conjTrace (Y * X)) ∧
      ∃ X : M2, conjTrace X ≠ Matrix.trace X := by
  refine ⟨by simp [Matrix.trace_one, Complex.ext_iff], ?_, ?_⟩
  · intro X Y
    simp [Matrix.trace_mul_comm X Y]
  · refine ⟨Complex.I • (1 : M2), ?_⟩
    simp [Matrix.trace_smul, Matrix.trace_one, Complex.ext_iff]
    norm_num

end Task7
