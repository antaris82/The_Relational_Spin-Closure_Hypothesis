import Mathlib

/-!
# The Hermitian `2 × 2` complex carrier `Herm₂(ℂ)`

This file constructs the real four-dimensional carrier of `3+1` Minkowski geometry inside the
associative algebra `M₂(ℂ)`, purely algebraically:

* `Herm2.hMat T X Y Z` — the Hermitian matrix with the stated coordinates, and
  `Herm2.hermCoordEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)`;
* `Herm2.det_coords` — the determinant *is* the Minkowski quadratic form `T² - X² - Y² - Z²`;
* the Pauli matrices, their Hermiticity, the basis theorem and the anticommutation relations;
* the diagonal split subalgebra `ℝ × ℝ ↪ M₂(ℂ)` with its two idempotents, recovering the
  `1+1` split carrier as an exact substructure;
* the off-diagonal (cross-sector) complement, noncommutativity of the ambient algebra, and the
  rank obstruction that forbids writing the `3+1` form as a product of two real linear forms.

No physical interpretation is asserted anywhere.  `T, X, Y, Z` are coordinate symbols.
-/

noncomputable section

open Matrix Complex

namespace Herm2

/-- The ambient associative algebra `M₂(ℂ)`. -/
abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- The Hermitian carrier, as the real subspace of self-adjoint elements of `M₂(ℂ)`.
It is **not** a subalgebra: products of Hermitian matrices need not be Hermitian
(see `Herm2.mul_not_hermitian`). -/
abbrev Herm : Type := selfAdjoint M2

/-! ## Section 2 : the Hermitian coordinate equivalence -/

/-- `H(T, X, Y, Z) = !![T + Z, X - iY; X + iY, T - Z]`. -/
def hMat (T X Y Z : ℝ) : M2 :=
  !![((T + Z : ℝ) : ℂ), (X : ℂ) - (Y : ℝ) * I; (X : ℝ) + (Y : ℝ) * I, ((T - Z : ℝ) : ℂ)]

@[simp] theorem hMat_00 (T X Y Z : ℝ) : hMat T X Y Z 0 0 = ((T + Z : ℝ) : ℂ) := rfl
@[simp] theorem hMat_01 (T X Y Z : ℝ) : hMat T X Y Z 0 1 = (X : ℂ) - (Y : ℝ) * I := rfl
@[simp] theorem hMat_10 (T X Y Z : ℝ) : hMat T X Y Z 1 0 = (X : ℂ) + (Y : ℝ) * I := rfl
@[simp] theorem hMat_11 (T X Y Z : ℝ) : hMat T X Y Z 1 1 = ((T - Z : ℝ) : ℂ) := rfl

/-- `H(T, X, Y, Z)` is Hermitian. -/
theorem hMat_isHermitian (T X Y Z : ℝ) : (hMat T X Y Z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- The Hermitian matrix `H(T, X, Y, Z)` as an element of the real subspace `Herm`. -/
def hHerm (T X Y Z : ℝ) : Herm :=
  ⟨hMat T X Y Z, (Matrix.isHermitian_iff_isSelfAdjoint).1 (hMat_isHermitian T X Y Z)⟩

@[simp] theorem coe_hHerm (T X Y Z : ℝ) : ((hHerm T X Y Z : Herm) : M2) = hMat T X Y Z := rfl

theorem hMat_add (T X Y Z T' X' Y' Z' : ℝ) :
    hMat (T + T') (X + X') (Y + Y') (Z + Z') = hMat T X Y Z + hMat T' X' Y' Z' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hMat, Complex.ext_iff] <;> ring

theorem hMat_smul (r T X Y Z : ℝ) :
    hMat (r * T) (r * X) (r * Y) (r * Z) = r • hMat T X Y Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Complex.ext_iff, Matrix.smul_apply, Complex.real_smul] <;> ring

/-- The coordinates of an arbitrary `2 × 2` complex matrix; for Hermitian matrices these are
the unique coordinates in the `H(T, X, Y, Z)` representation. -/
def coordsOf (H : M2) : Fin 4 → ℝ :=
  ![((H 0 0).re + (H 1 1).re) / 2, (H 1 0).re, (H 1 0).im, ((H 0 0).re - (H 1 1).re) / 2]

@[simp] theorem coordsOf_hMat (T X Y Z : ℝ) : coordsOf (hMat T X Y Z) = ![T, X, Y, Z] := by
  funext i
  fin_cases i <;> simp [coordsOf, hMat] <;> ring

/-- Every Hermitian matrix is `H` of its coordinates. -/
theorem hMat_coordsOf {H : M2} (h : H.IsHermitian) :
    hMat (coordsOf H 0) (coordsOf H 1) (coordsOf H 2) (coordsOf H 3) = H := by
  have h00 : (H 0 0).im = 0 := by
    have := congrFun (congrFun h 0) 0
    simp [Matrix.conjTranspose_apply, Complex.ext_iff] at this
    linarith
  have h11 : (H 1 1).im = 0 := by
    have := congrFun (congrFun h 1) 1
    simp [Matrix.conjTranspose_apply, Complex.ext_iff] at this
    linarith
  have h01 : H 0 1 = starRingEnd ℂ (H 1 0) := by
    have := congrFun (congrFun h 0) 1
    simpa [Matrix.conjTranspose_apply] using this.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, coordsOf, Complex.ext_iff, h01, h00, h11] <;> ring

/-- **Section 2.** The real-linear equivalence `ℝ⁴ ≃ Herm₂(ℂ)`. -/
def hermCoordEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] Herm where
  toFun v := hHerm (v 0) (v 1) (v 2) (v 3)
  map_add' v w := by
    apply Subtype.ext
    simpa using hMat_add (v 0) (v 1) (v 2) (v 3) (w 0) (w 1) (w 2) (w 3)
  map_smul' r v := by
    apply Subtype.ext
    simpa using hMat_smul r (v 0) (v 1) (v 2) (v 3)
  invFun H := coordsOf (H : M2)
  left_inv v := by
    funext i
    fin_cases i <;> simp [coordsOf_hMat]
  right_inv H := by
    apply Subtype.ext
    exact hMat_coordsOf ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)

@[simp] theorem hermCoordEquiv_apply (v : Fin 4 → ℝ) :
    ((hermCoordEquiv v : Herm) : M2) = hMat (v 0) (v 1) (v 2) (v 3) := rfl

@[simp] theorem hermCoordEquiv_symm_apply (H : Herm) :
    hermCoordEquiv.symm H = coordsOf (H : M2) := rfl

theorem hermCoordEquiv_hMat (T X Y Z : ℝ) :
    hermCoordEquiv ![T, X, Y, Z] = hHerm T X Y Z := rfl

/-- Uniqueness of the coordinate representation of a Hermitian matrix. -/
theorem existsUnique_coords {H : M2} (h : H.IsHermitian) :
    ∃! v : Fin 4 → ℝ, hMat (v 0) (v 1) (v 2) (v 3) = H := by
  refine ⟨coordsOf H, hMat_coordsOf h, ?_⟩
  intro w hw
  have : coordsOf (hMat (w 0) (w 1) (w 2) (w 3)) = coordsOf H := by rw [hw]
  rw [coordsOf_hMat] at this
  funext i
  have hi := congrFun this i
  fin_cases i <;> simpa using hi

/-! ## Section 3 : the determinant is the Minkowski quadratic form -/

/-- The `3+1` Minkowski quadratic form on `ℝ⁴`. -/
def Qform (v : Fin 4 → ℝ) : ℝ := v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2

theorem Qform_apply (T X Y Z : ℝ) : Qform ![T, X, Y, Z] = T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := by
  simp [Qform]

/-- The intermediate step `(X - iY)(X + iY) = X² + Y²`. -/
theorem offdiag_mul (X Y : ℝ) :
    ((X : ℂ) - (Y : ℝ) * I) * ((X : ℂ) + (Y : ℝ) * I) = ((X ^ 2 + Y ^ 2 : ℝ) : ℂ) := by
  simp [Complex.ext_iff, ← Complex.ofReal_pow]
  constructor <;> ring

/-- `det H = (T+Z)(T-Z) - (X-iY)(X+iY)`, the raw `2 × 2` expansion. -/
theorem det_hMat_expand (T X Y Z : ℝ) :
    (hMat T X Y Z).det =
      ((T + Z : ℝ) : ℂ) * ((T - Z : ℝ) : ℂ)
        - ((X : ℂ) - (Y : ℝ) * I) * ((X : ℂ) + (Y : ℝ) * I) := by
  simp [hMat, Matrix.det_fin_two_of]

/-- **Section 3.** `det H(T, X, Y, Z) = T² - X² - Y² - Z²`. -/
theorem det_hMat (T X Y Z : ℝ) :
    (hMat T X Y Z).det = ((T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 : ℝ) : ℂ) := by
  rw [det_hMat_expand, offdiag_mul]
  push_cast
  ring

/-- **Section 3, packaged form.** The determinant of the Hermitian matrix with coordinate
vector `v` is the Minkowski quadratic form of `v`. -/
theorem det_coords (v : Fin 4 → ℝ) :
    ((hermCoordEquiv v : Herm) : M2).det = ((Qform v : ℝ) : ℂ) := by
  simpa [Qform] using det_hMat (v 0) (v 1) (v 2) (v 3)

/-- The determinant of a Hermitian matrix is real. -/
theorem det_isReal_of_isHermitian {H : M2} (h : H.IsHermitian) : (H.det).im = 0 := by
  have : star H.det = H.det := by
    rw [← Matrix.det_conjTranspose, h]
  have h2 := congrArg Complex.im this
  simp [Complex.star_def] at h2
  linarith

/-! ## Sections 4, 5, 8 : the diagonal split sector and the off-diagonal complement -/

/-- The first diagonal idempotent. -/
def PP : M2 := !![1, 0; 0, 0]

/-- The second diagonal idempotent. -/
def PM : M2 := !![0, 0; 0, 1]

/-- The upper-right matrix unit. -/
def E12 : M2 := !![0, 1; 0, 0]

/-- The lower-left matrix unit. -/
def E21 : M2 := !![0, 0; 1, 0]

theorem PP_sq : PP * PP = PP := by ext i j; fin_cases i <;> fin_cases j <;> simp [PP, mul_apply, Fin.sum_univ_succ]
theorem PM_sq : PM * PM = PM := by ext i j; fin_cases i <;> fin_cases j <;> simp [PM, mul_apply, Fin.sum_univ_succ]
theorem PP_mul_PM : PP * PM = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [PP, PM, mul_apply, Fin.sum_univ_succ]
theorem PM_mul_PP : PM * PP = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [PP, PM, mul_apply, Fin.sum_univ_succ]
theorem PP_add_PM : PP + PM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PP, PM, Matrix.one_apply]

/-- The diagonal matrix `D(u, v) = u P + v Q`. -/
def D (u v : ℝ) : M2 := !![(u : ℂ), 0; 0, (v : ℂ)]

theorem D_eq (u v : ℝ) : D u v = (u : ℂ) • PP + (v : ℂ) • PM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D, PP, PM]

theorem det_D (u v : ℝ) : (D u v).det = ((u * v : ℝ) : ℂ) := by
  simp [D, Matrix.det_fin_two_of]

/-- The diagonal split carrier sits inside the Hermitian carrier as the locus `X = Y = 0`. -/
theorem D_eq_hMat (T Z : ℝ) : D (T + Z) (T - Z) = hMat T 0 0 Z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D, hMat]

theorem det_D_TZ (T Z : ℝ) : (D (T + Z) (T - Z)).det = ((T ^ 2 - Z ^ 2 : ℝ) : ℂ) := by
  rw [det_D]; push_cast; ring

/-- **Section 4.** The diagonal embedding of the `1+1` split carrier `ℝ × ℝ` into `M₂(ℂ)`,
as a morphism of unital real algebras. -/
def diagEmb : (ℝ × ℝ) →ₐ[ℝ] M2 where
  toFun p := D p.1 p.2
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [D, Matrix.one_apply]
  map_mul' p q := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [D, mul_apply, Fin.sum_univ_succ, Complex.ext_iff] <;> ring
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [D]
  map_add' p q := by ext i j; fin_cases i <;> fin_cases j <;> simp [D, Complex.ext_iff]
  commutes' r := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [D, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

@[simp] theorem diagEmb_apply (u v : ℝ) : diagEmb (u, v) = D u v := rfl

theorem diagEmb_injective : Function.Injective diagEmb := by
  intro p q h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  simp [diagEmb, D] at h0 h1
  exact Prod.ext h0 h1

theorem diagEmb_ePlus : diagEmb (1, 0) = PP := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagEmb, D, PP]

theorem diagEmb_eMinus : diagEmb (0, 1) = PM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagEmb, D, PM]

/-- The diagonal embedding carries the split norm `uv` to the determinant. -/
theorem det_diagEmb (p : ℝ × ℝ) : (diagEmb p).det = ((p.1 * p.2 : ℝ) : ℂ) := det_D p.1 p.2

theorem diagEmb_isHermitian (p : ℝ × ℝ) : (diagEmb p).IsHermitian := by
  have h : diagEmb p = hMat ((p.1 + p.2) / 2) 0 0 ((p.1 - p.2) / 2) := by
    rw [← D_eq_hMat]
    show D p.1 p.2 = _
    congr 1 <;> ring
  rw [h]
  exact hMat_isHermitian _ _ _ _

/-! ### Cross-sector relations (Section 8) -/

theorem PP_mul_E12 : PP * E12 = E12 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PP, E12, mul_apply, Fin.sum_univ_succ]
theorem E12_mul_PM : E12 * PM = E12 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PM, E12, mul_apply, Fin.sum_univ_succ]
theorem PM_mul_E21 : PM * E21 = E21 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PM, E21, mul_apply, Fin.sum_univ_succ]
theorem E21_mul_PP : E21 * PP = E21 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PP, E21, mul_apply, Fin.sum_univ_succ]
theorem E12_mul_PP : E12 * PP = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PP, E12, mul_apply, Fin.sum_univ_succ]
theorem PM_mul_E12 : PM * E12 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PM, E12, mul_apply, Fin.sum_univ_succ]
theorem PP_mul_E21 : PP * E21 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PP, E21, mul_apply, Fin.sum_univ_succ]
theorem E21_mul_PM : E21 * PM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [PM, E21, mul_apply, Fin.sum_univ_succ]

/-- **Section 8 / 23.** The ambient algebra is noncommutative. -/
theorem PP_E12_ne_E12_PP : PP * E12 ≠ E12 * PP := by
  rw [PP_mul_E12, E12_mul_PP]
  intro h
  have := congrFun (congrFun h 0) 1
  simp [E12] at this

/-- The diagonal split subalgebra is commutative. -/
theorem diag_commute (p q : ℝ × ℝ) : diagEmb p * diagEmb q = diagEmb q * diagEmb p := by
  rw [← map_mul, ← map_mul, mul_comm]

/-- The off-diagonal Hermitian contribution `z E₁₂ + z̄ E₂₁`. -/
def offDiag (z : ℂ) : M2 := z • E12 + (starRingEnd ℂ z) • E21

theorem offDiag_isHermitian (z : ℂ) : (offDiag z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [offDiag, E12, E21, Matrix.conjTranspose_apply]

/-- **Section 8.** Exact decomposition of a Hermitian matrix into two real diagonal
coordinates and one complex off-diagonal coordinate. -/
theorem herm_decomposition (T X Y Z : ℝ) :
    hMat T X Y Z = ((T + Z : ℝ) : ℂ) • PP + ((T - Z : ℝ) : ℂ) • PM
      + offDiag ((X : ℂ) - (Y : ℝ) * I) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, PP, PM, offDiag, E12, E21, Complex.ext_iff]

/-- Conversely every Hermitian matrix has that shape, with the coordinates uniquely determined:
the off-diagonal part contributes exactly the two real degrees of freedom `Re z`, `Im z`. -/
theorem offDiag_injective : Function.Injective offDiag := by
  intro z w h
  have := congrFun (congrFun h 0) 1
  simpa [offDiag, E12, E21] using this

/-- The off-diagonal coordinate space `ℂ` is real-linearly `ℝ²`: two real degrees of freedom. -/
def offDiagEquiv : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  Complex.basisOneI.equivFun

/-! ## Sections 5, 6, 7 : the Pauli matrices -/

def sigma0 : M2 := 1
def sigma1 : M2 := !![0, 1; 1, 0]
def sigma2 : M2 := !![0, -I; I, 0]
def sigma3 : M2 := !![1, 0; 0, -1]

/-- The four Pauli matrices indexed by `Fin 4`. -/
def sigmaF : Fin 4 → M2 := ![sigma0, sigma1, sigma2, sigma3]

theorem sigma0_isHermitian : sigma0.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma0, Matrix.one_apply, Matrix.conjTranspose_apply]
theorem sigma1_isHermitian : sigma1.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma1, Matrix.conjTranspose_apply]
theorem sigma2_isHermitian : sigma2.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma2, Matrix.conjTranspose_apply]
theorem sigma3_isHermitian : sigma3.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma3, Matrix.conjTranspose_apply]

theorem sigmaF_isHermitian (i : Fin 4) : (sigmaF i).IsHermitian := by
  fin_cases i
  · exact sigma0_isHermitian
  · exact sigma1_isHermitian
  · exact sigma2_isHermitian
  · exact sigma3_isHermitian

/-- **Section 5.** The split generator `ε = p - q` is represented by `σ₃`. -/
theorem sigma3_eq_PP_sub_PM : sigma3 = PP - PM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma3, PP, PM]

theorem sigma3_sq : sigma3 * sigma3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3, mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- **Section 6.** The coordinate representation in the Pauli basis. -/
theorem hMat_eq_pauli (T X Y Z : ℝ) :
    hMat T X Y Z = T • sigma0 + X • sigma1 + Y • sigma2 + Z • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, sigma0, sigma1, sigma2, sigma3, Matrix.one_apply, Complex.ext_iff,
      Complex.real_smul] <;> ring

/-- The Pauli matrices as elements of the real vector space `Herm`. -/
def sigmaH (i : Fin 4) : Herm :=
  ⟨sigmaF i, (Matrix.isHermitian_iff_isSelfAdjoint).1 (sigmaF_isHermitian i)⟩

/-- **Section 6.** `{σ₀, σ₁, σ₂, σ₃}` is an `ℝ`-basis of `Herm₂(ℂ)`, and it is the basis
corresponding to the coordinate equivalence of Section 2. -/
def pauliBasis : Module.Basis (Fin 4) ℝ Herm :=
  (Pi.basisFun ℝ (Fin 4)).map hermCoordEquiv

theorem pauliBasis_apply (i : Fin 4) : pauliBasis i = sigmaH i := by
  apply Subtype.ext
  fin_cases i <;>
    · show hMat _ _ _ _ = _
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [sigmaH, sigmaF, sigma0, sigma1, sigma2, sigma3, hMat, Matrix.one_apply,
          Pi.basisFun_apply, Complex.ext_iff]

/-- **Section 7.** The Pauli anticommutation relations `σᵢσⱼ + σⱼσᵢ = 2δᵢⱼ I` for spatial
indices `i, j ∈ {1, 2, 3}`. -/
theorem pauli_anticommute (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
    sigmaF i * sigmaF j + sigmaF j * sigmaF i = (if i = j then (2 : ℂ) else 0) • (1 : M2) := by
  fin_cases i <;> fin_cases j <;> simp_all <;>
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [sigmaF, sigma1, sigma2, sigma3, mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
          Complex.ext_iff] <;> ring

theorem pauli_sq (i : Fin 4) (hi : i ≠ 0) : sigmaF i * sigmaF i = 1 := by
  fin_cases i <;> simp_all <;>
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [sigmaF, sigma1, sigma2, sigma3, mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
          Complex.ext_iff] <;> ring

theorem pauli_anticomm_of_ne (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    sigmaF i * sigmaF j = - (sigmaF j * sigmaF i) := by
  have := pauli_anticommute i j hi hj
  rw [if_neg hij] at this
  simp at this
  linear_combination (norm := module) this

/-! ## Section 23 : products of Hermitian matrices, and left multiplication -/

/-- Ordinary left multiplication does not preserve the Hermitian carrier: `σ₁σ₃` is not
Hermitian although `σ₁` and `σ₃` are. -/
theorem mul_not_hermitian : ¬ (sigma1 * sigma3).IsHermitian := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [sigma1, sigma3, mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply] at this
  exact absurd this (by norm_num)

/-! ## Section 21 : the `3+1` form is not a product of two real linear forms -/

theorem Qform_factors_1_1 (T Z : ℝ) : T ^ 2 - Z ^ 2 = (T + Z) * (T - Z) := by ring

/-- **Section 21.** The `3+1` Minkowski form is *not* the product of two real linear forms on
`ℝ⁴`; hence the two-linear-factor mechanism of the `1+1` construction cannot represent it. -/
theorem Qform_not_product_of_linear_forms
    (f g : (Fin 4 → ℝ) →ₗ[ℝ] ℝ) : ¬ (∀ v, Qform v = f v * g v) := by
  intro h
  -- find a nonzero purely spatial vector in the kernel of `f`
  obtain ⟨v, hv0, hvne, hfv⟩ :
      ∃ v : Fin 4 → ℝ, v 0 = 0 ∧ v ≠ 0 ∧ f v = 0 := by
    let a : Fin 4 → ℝ := ![0, 1, 0, 0]
    let b : Fin 4 → ℝ := ![0, 0, 1, 0]
    by_cases h1 : f a = 0
    · refine ⟨a, by simp [a], ?_, h1⟩
      intro hc
      have := congrFun hc 1
      simp [a] at this
    · refine ⟨f b • a - f a • b, by simp [a, b], ?_, ?_⟩
      · intro hc
        have := congrFun hc 2
        simp [a, b, Pi.sub_apply, Pi.smul_apply] at this
        exact h1 (by linarith)
      · simp [map_sub, map_smul]
        ring
  have := h v
  rw [hfv, zero_mul] at this
  rw [Qform, hv0] at this
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have h3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  exact hvne (by funext i; fin_cases i <;> simp [hv0, h1, h2, h3])

end Herm2
