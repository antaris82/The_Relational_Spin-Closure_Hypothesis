import Mathlib
import RequestProject.Experiment1.Task7Cone

/-!
# Task 7, Part F : is the associative multiplication primitive?

Everything in this file is stated for the rank-two Hermitian Jordan algebra
`J = Herm₂(ℂ)` with `H ∘ K = (HK + KH)/2`.

* **F1** the trace is definable from the Jordan product alone, through the Jordan regular
  representation `L_H : K ↦ H ∘ K` on the *real* four-dimensional carrier:
  `LinearMap.trace ℝ Herm (jordanL H) = 2 * (Matrix.trace H).re`.
  Combined with `Task7.det_eq_trace_formula` and `Task7.jordan_cayleyHamilton`, the quadratic
  norm, the adjugate, the polarized Minkowski form and the positive cone are then all Jordan
  notions (see `Task7Polarization` and `Task7Cone`).
* **F2** `M₂(ℂ)` is generated *as a real associative algebra* by its Hermitian part, so the
  associative envelope of the Jordan carrier is at least not larger than `M₂(ℂ)`.
* **F3** the envelope is **not** unique: the opposite product `X *ᵒᵖ Y = Y X` is a different
  associative unital multiplication on the same real vector space inducing exactly the same
  Jordan product.  Hence associative multiplication is *not* derivable from Jordan data.
-/

noncomputable section

open Matrix Complex Herm2

namespace Task7

/-! ## F1 : the Jordan regular representation and the trace -/

/-- The Jordan product in Hermitian coordinates:
the `0`-component is the Euclidean inner product, the spatial components are `v₀ w + w₀ v`. -/
theorem hMat_jordan (a b c d a' b' c' d' : ℝ) :
    Carrier.jordan (hMat a b c d) (hMat a' b' c' d')
      = hMat (a * a' + b * b' + c * c' + d * d') (a * b' + b * a') (a * c' + c * a')
          (a * d' + d * a') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Carrier.jordan, hMat, Complex.ext_iff,
      Complex.inv_re, Complex.inv_im, Complex.normSq] <;>
    refine ⟨?_, ?_⟩ <;> first | trivial | ring

theorem jordan_add_right (H K L : M2) :
    Carrier.jordan H (K + L) = Carrier.jordan H K + Carrier.jordan H L := by
  simp only [Carrier.jordan, mul_add, add_mul]
  module

theorem jordan_smul_right (r : ℝ) (H K : M2) :
    Carrier.jordan H (r • K) = r • Carrier.jordan H K := by
  simp only [Carrier.jordan, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [smul_comm r ((2:ℂ)⁻¹) (H * K), smul_comm r ((2:ℂ)⁻¹) (K * H)]

/-- The Jordan product as an operation on the real carrier `Herm = selfAdjoint M₂(ℂ)`. -/
def jH (H K : Herm) : Herm :=
  ⟨Carrier.jordan (H : M2) (K : M2),
    (Matrix.isHermitian_iff_isSelfAdjoint).1
      (Carrier.jordanProduct_mem_selfAdjoint
        ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)
        ((Matrix.isHermitian_iff_isSelfAdjoint).2 K.2))⟩

@[simp] theorem coe_jH (H K : Herm) : ((jH H K : Herm) : M2) = Carrier.jordan (H : M2) (K : M2) :=
  rfl

/-- **F1.** The Jordan regular representation `L_H : K ↦ H ∘ K`, a real-linear endomorphism of
the four-dimensional carrier.  Only the Jordan product is used. -/
def jordanL (H : Herm) : Herm →ₗ[ℝ] Herm where
  toFun K := jH H K
  map_add' K L := by
    apply Subtype.ext
    simpa using jordan_add_right (H : M2) (K : M2) (L : M2)
  map_smul' r K := by
    apply Subtype.ext
    simpa using jordan_smul_right r (H : M2) (K : M2)

@[simp] theorem jordanL_apply (H K : Herm) : jordanL H K = jH H K := rfl

/-- The coordinate basis of the Hermitian carrier. -/
def hBasis : Module.Basis (Fin 4) ℝ Herm := (Pi.basisFun ℝ (Fin 4)).map hermCoordEquiv

theorem hBasis_apply (i : Fin 4) :
    ((hBasis i : Herm) : M2) = hMat (Pi.basisFun ℝ (Fin 4) i 0) (Pi.basisFun ℝ (Fin 4) i 1)
      (Pi.basisFun ℝ (Fin 4) i 2) (Pi.basisFun ℝ (Fin 4) i 3) := rfl

theorem hBasis_repr (H : Herm) (i : Fin 4) : hBasis.repr H i = coordsOf (H : M2) i := rfl

/-- **F1.** The trace of the Jordan regular representation of `H` is `4 T`, where `T` is the
`0`-coordinate of `H`; equivalently `2 · tr H`.  The right-hand side of the statement is the
matrix trace, but the left-hand side uses **only** the Jordan product, so the trace functional
is definable from Jordan data. -/
theorem trace_jordanL (H : Herm) :
    LinearMap.trace ℝ Herm (jordanL H) = 4 * coordsOf (H : M2) 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ hBasis]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, jordanL_apply]
  have hH : hMat (coordsOf (H : M2) 0) (coordsOf (H : M2) 1) (coordsOf (H : M2) 2)
      (coordsOf (H : M2) 3) = (H : M2) :=
    hMat_coordsOf ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)
  have key : ∀ i : Fin 4, hBasis.repr (jH H (hBasis i)) i = coordsOf (H : M2) 0 := by
    intro i
    rw [hBasis_repr]
    have : ((jH H (hBasis i) : Herm) : M2)
        = Carrier.jordan (hMat (coordsOf (H : M2) 0) (coordsOf (H : M2) 1) (coordsOf (H : M2) 2)
            (coordsOf (H : M2) 3)) ((hBasis i : Herm) : M2) := by
      rw [coe_jH, hH]
    rw [this, hBasis_apply]
    fin_cases i <;>
      simp [hMat_jordan, Pi.basisFun_apply, coordsOf_hMat]
  simp only [key]
  simp [Finset.sum_const]

/-- `4 T = 2 tr H`. -/
theorem coordsOf_zero_eq (H : M2) :
    4 * coordsOf H 0 = 2 * (Matrix.trace H).re := by
  simp [coordsOf, Matrix.trace, Fin.sum_univ_succ]
  ring

/-- **F1, final form.** The matrix trace is recovered from the Jordan regular representation. -/
theorem trace_from_jordan (H : Herm) :
    LinearMap.trace ℝ Herm (jordanL H) = 2 * (Matrix.trace (H : M2)).re := by
  rw [trace_jordanL, coordsOf_zero_eq]

/-! ## F2 : the associative envelope -/

/-- `σ₁σ₂σ₃ = i·I`, the element that produces the complex scalars from Hermitian generators. -/
theorem sigma_product : sigma1 * sigma2 * sigma3 = Complex.I • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **F2.** `M₂(ℂ)` is generated as a *real* associative unital algebra by its Hermitian part:
the associative envelope of the Jordan carrier is `M₂(ℂ)` itself. -/
theorem adjoin_hermitian_eq_top :
    Algebra.adjoin ℝ {X : M2 | X.IsHermitian} = ⊤ := by
  rw [eq_top_iff]
  rintro X -
  have h1 : sigma1 ∈ Algebra.adjoin ℝ {X : M2 | X.IsHermitian} :=
    Algebra.subset_adjoin sigma1_isHermitian
  have h2 : sigma2 ∈ Algebra.adjoin ℝ {X : M2 | X.IsHermitian} :=
    Algebra.subset_adjoin sigma2_isHermitian
  have h3 : sigma3 ∈ Algebra.adjoin ℝ {X : M2 | X.IsHermitian} :=
    Algebra.subset_adjoin sigma3_isHermitian
  have hI : Complex.I • (1 : M2) ∈ Algebra.adjoin ℝ {X : M2 | X.IsHermitian} := by
    rw [← sigma_product]
    exact mul_mem (mul_mem h1 h2) h3
  have hA : Carrier.herPart X ∈ Algebra.adjoin ℝ {X : M2 | X.IsHermitian} :=
    Algebra.subset_adjoin (Carrier.herPart_isHermitian X)
  have hB : Carrier.antiPart X ∈ Algebra.adjoin ℝ {X : M2 | X.IsHermitian} :=
    Algebra.subset_adjoin (Carrier.antiPart_isHermitian X)
  have hmul : Complex.I • Carrier.antiPart X
      = (Complex.I • (1 : M2)) * Carrier.antiPart X := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [Carrier.hermitian_decomposition X, hmul]
  exact add_mem hA (mul_mem hI hB)

/-! ## F3 : the envelope is not unique -/

/-- The opposite multiplication on the same real vector space. -/
def mulOp (X Y : M2) : M2 := Y * X

theorem mulOp_assoc (X Y Z : M2) : mulOp (mulOp X Y) Z = mulOp X (mulOp Y Z) := by
  simp only [mulOp, Matrix.mul_assoc]

theorem mulOp_one (X : M2) : mulOp X 1 = X ∧ mulOp 1 X = X := by
  simp [mulOp]

/-- The opposite product induces exactly the same Jordan product. -/
theorem jordan_mulOp (X Y : M2) :
    (2 : ℂ)⁻¹ • (mulOp X Y + mulOp Y X) = Carrier.jordan X Y := by
  simp only [mulOp, Carrier.jordan, add_comm]

/-- **F3.** The two associative products differ, although they have the same unit and the same
symmetrization.  Hence the associative multiplication is *not* determined by the Jordan
structure: it is at best canonical up to passing to the opposite algebra. -/
theorem mulOp_ne_mul : ∃ X Y : M2, mulOp X Y ≠ X * Y := by
  refine ⟨PP, E12, ?_⟩
  simp only [mulOp]
  exact fun h => PP_E12_ne_E12_PP h.symm

/-- **F3, summary.** Associativity/multiplication is not recoverable from the Jordan product
alone; but the Jordan product *is* recoverable from either associative product. -/
theorem jordan_not_determining_mul :
    (∀ X Y : M2, Carrier.jordan X Y = (2 : ℂ)⁻¹ • (mulOp X Y + mulOp Y X)) ∧
      (∃ X Y : M2, mulOp X Y ≠ X * Y) :=
  ⟨fun X Y => (jordan_mulOp X Y).symm, mulOp_ne_mul⟩

end Task7
