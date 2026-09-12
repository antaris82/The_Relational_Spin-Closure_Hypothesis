import Mathlib
import RequestProject.Experiment1.Task6Cone
import RequestProject.Experiment1.Task7Polarization

/-!
# Task 7, Part B : the positive cone from Jordan data alone

The Task-6 cone was the matrix PSD cone `𝒫 = {H : H ⪰ 0}`, i.e. an *order* notion imported
from the ambient complex Hilbert space.  Here it is reconstructed from Jordan-algebraic data:

* `B1` `𝒞_sq = 𝒫`: the Hermitian matrices that are Jordan squares are exactly the PSD ones.
  The square-root direction is **constructed explicitly** from the Cayley–Hamilton identity
  (no appeal to a spectral theorem or to a library square root).
* `B2` `H ⪰ 0 ↔ tr H ≥ 0 ∧ N_J(H) ≥ 0` — positivity via trace and the quadratic norm only.
* `B3` the cone of squares is pointed and contains `I` but not `-I`, so the *Jordan* data do
  distinguish the two opposite cones; the quadratic norm alone does not (`NJr_neg`).

No Lorentz group and no determinant-preserving group appear anywhere in this file.
-/

noncomputable section

open Matrix Complex Herm2
open scoped ComplexOrder

namespace Task7

/-! ## The square of a Hermitian matrix in coordinates -/

/-- The Jordan square in coordinates:
`H(T,X,Y,Z)² = H(T² + X² + Y² + Z², 2TX, 2TY, 2TZ)`. -/
theorem hMat_sq (T X Y Z : ℝ) :
    hMat T X Y Z * hMat T X Y Z
      = hMat (T ^ 2 + X ^ 2 + Y ^ 2 + Z ^ 2) (2 * T * X) (2 * T * Y) (2 * T * Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Matrix.mul_apply, Fin.sum_univ_succ, Complex.ext_iff,
      -Complex.ofReal_pow] <;> constructor <;> ring_nf

/-- Jordan square = associative square on the Hermitian carrier. -/
theorem jordan_self (H : M2) : Carrier.jordan H H = H * H := jordan_sq H

/-! ## B1 : the cone of Jordan squares -/

/-- The intrinsic cone of Jordan squares
`𝒞_sq = {H ∈ Herm₂(ℂ) : ∃ K Hermitian, H = K ∘ K}`. -/
def SquareCone : Set M2 :=
  {H | H.IsHermitian ∧ ∃ K : M2, K.IsHermitian ∧ H = Carrier.jordan K K}

theorem mem_squareCone_iff (H : M2) :
    H ∈ SquareCone ↔ H.IsHermitian ∧ ∃ K : M2, K.IsHermitian ∧ H = K * K := by
  constructor
  · rintro ⟨hH, K, hK, rfl⟩
    exact ⟨hH, K, hK, jordan_self K⟩
  · rintro ⟨hH, K, hK, rfl⟩
    exact ⟨hH, K, hK, (jordan_self K).symm⟩

/-- **B1, easy direction.** A Jordan square is positive semidefinite. -/
theorem posSemidef_of_mem_squareCone {H : M2} (h : H ∈ SquareCone) : H.PosSemidef := by
  obtain ⟨_, K, hK, rfl⟩ := (mem_squareCone_iff H).1 h
  have := Matrix.posSemidef_conjTranspose_mul_self K
  rwa [hK.eq] at this

/-- **B1, hard direction (explicit square root).**  Every positive semidefinite `2 × 2`
Hermitian matrix is the Jordan square of a Hermitian matrix.  The square root is written
down explicitly from the coordinates, so the proof is self-contained: no spectral theorem
and no library matrix square root is used. -/
theorem exists_sqrt_of_psd_coords {T X Y Z : ℝ} (h : (hMat T X Y Z).PosSemidef) :
    ∃ a b c d : ℝ, hMat T X Y Z = hMat a b c d * hMat a b c d := by
  obtain ⟨hT, hQ⟩ := (Carrier.psd_iff_futureCone T X Y Z).1 h
  set n : ℝ := Real.sqrt (T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2) with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hn2 : n ^ 2 = T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := Real.sq_sqrt hQ
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · -- `T = 0` forces `H = 0`
    have hX : X = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg Z]
    have hY : Y = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg Z]
    have hZ : Z = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg Z]
    refine ⟨0, 0, 0, 0, ?_⟩
    rw [hMat_sq, ← hT0, hX, hY, hZ]
    norm_num
  · have hpos : 0 < (T + n) / 2 := by linarith
    set s : ℝ := Real.sqrt ((T + n) / 2) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hpos
    have hs2 : s ^ 2 = (T + n) / 2 := Real.sq_sqrt (le_of_lt hpos)
    refine ⟨s, X / (2 * s), Y / (2 * s), Z / (2 * s), ?_⟩
    rw [hMat_sq]
    have hsne : (2 * s) ≠ 0 := by positivity
    have h1 : s ^ 2 + (X / (2 * s)) ^ 2 + (Y / (2 * s)) ^ 2 + (Z / (2 * s)) ^ 2 = T := by
      field_simp
      nlinarith [hs2, hn2, hspos]
    have h2 : 2 * s * (X / (2 * s)) = X := by field_simp
    have h3 : 2 * s * (Y / (2 * s)) = Y := by field_simp
    have h4 : 2 * s * (Z / (2 * s)) = Z := by field_simp
    rw [h1, h2, h3, h4]

/-- **B1.**  `𝒞_sq = 𝒫`: the cone of Jordan squares *is* the positive semidefinite cone. -/
theorem squareCone_eq_psd : SquareCone = {H : M2 | H.PosSemidef} := by
  ext H
  constructor
  · exact posSemidef_of_mem_squareCone
  · intro h
    have hH : H.IsHermitian := h.1
    obtain ⟨v, hv⟩ : ∃ v : Fin 4 → ℝ, hMat (v 0) (v 1) (v 2) (v 3) = H :=
      ⟨coordsOf H, hMat_coordsOf hH⟩
    rw [← hv] at h ⊢
    obtain ⟨a, b, c, d, hsq⟩ := exists_sqrt_of_psd_coords h
    refine ⟨hMat_isHermitian _ _ _ _, hMat a b c d, hMat_isHermitian a b c d, ?_⟩
    rw [jordan_self]
    exact hsq

/-! ## B2 : positivity from trace and the quadratic norm -/

/-- **B2.**  For a Hermitian `2 × 2` matrix, positivity is equivalent to the two Jordan-data
inequalities `tr H ≥ 0` and `N_J(H) ≥ 0`.  Compare with the Task-6 coordinate statement
`T ≥ 0 ∧ T² - X² - Y² - Z² ≥ 0` (`Carrier.psd_iff_futureCone`): this is the coordinate-free
form of the same criterion. -/
theorem psd_iff_trace_and_norm_nonneg (H : Herm2.Herm) :
    ((H : M2)).PosSemidef ↔ 0 ≤ (Matrix.trace (H : M2)).re ∧ 0 ≤ NJr H := by
  obtain ⟨v, hv⟩ : ∃ v : Fin 4 → ℝ, hermCoordEquiv v = H :=
    ⟨hermCoordEquiv.symm H, hermCoordEquiv.apply_symm_apply H⟩
  subst hv
  have hcoe : ((hermCoordEquiv v : Herm2.Herm) : M2) = hMat (v 0) (v 1) (v 2) (v 3) :=
    hermCoordEquiv_apply v
  have htr : (Matrix.trace (hMat (v 0) (v 1) (v 2) (v 3))).re = 2 * v 0 := by
    simp [Matrix.trace, Fin.sum_univ_succ, hMat]
    ring
  rw [hcoe, Carrier.psd_iff_futureCone, htr, NJr_coords]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by simpa [Qform] using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by simpa [Qform] using h2⟩

/-! ## B3 : orientation -/

/-- The quadratic norm alone does **not** distinguish the two opposite cones. -/
theorem NJr_neg (H : Herm2.Herm) : NJr (-H) = NJr H := by
  simp [NJr, Matrix.det_fin_two]

/-- **B3.**  The unit is a Jordan square. -/
theorem one_mem_squareCone : (1 : M2) ∈ SquareCone := by
  refine ⟨Matrix.isHermitian_one, 1, Matrix.isHermitian_one, ?_⟩
  rw [jordan_self, mul_one]

/-- **B3.**  `-I` is *not* a Jordan square: the Jordan structure genuinely orients the cone. -/
theorem neg_one_not_mem_squareCone : (-1 : M2) ∉ SquareCone := by
  intro h
  have hpsd := posSemidef_of_mem_squareCone h
  rw [show ((-1 : M2)) = hMat (-1) 0 0 0 by
        ext i j; fin_cases i <;> fin_cases j <;> simp [hMat]] at hpsd
  obtain ⟨hT, -⟩ := (Carrier.psd_iff_futureCone (-1) 0 0 0).1 hpsd
  linarith

/-- **B3 (pointedness).**  `𝒞_sq ∩ (-𝒞_sq) = {0}`. -/
theorem squareCone_pointed {H : M2} (h₁ : H ∈ SquareCone) (h₂ : -H ∈ SquareCone) : H = 0 := by
  have p₁ := posSemidef_of_mem_squareCone h₁
  have p₂ := posSemidef_of_mem_squareCone h₂
  have hH : H.IsHermitian := p₁.1
  obtain ⟨v, hv⟩ : ∃ v : Fin 4 → ℝ, hMat (v 0) (v 1) (v 2) (v 3) = H :=
    ⟨coordsOf H, hMat_coordsOf hH⟩
  rw [← hv] at p₁ p₂ ⊢
  obtain ⟨hT, hQ⟩ := (Carrier.psd_iff_futureCone (v 0) (v 1) (v 2) (v 3)).1 p₁
  have hneg : -hMat (v 0) (v 1) (v 2) (v 3) = hMat (-v 0) (-v 1) (-v 2) (-v 3) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hMat, Complex.ext_iff] <;> ring
  rw [hneg] at p₂
  obtain ⟨hT', hQ'⟩ := (Carrier.psd_iff_futureCone _ _ _ _).1 p₂
  have hv0 : v 0 = 0 := by linarith
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  rw [hv0, hv1, hv2, hv3]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hMat]

/-- **B3 (orientation is canonical from the Jordan data, but only from them).**
The cone of Jordan squares contains `I` and not `-I`, hence the *ordered Jordan* structure
selects one of the two opposite cones; the quadratic norm by itself does not, since
`N_J(-H) = N_J(H)`. -/
theorem orientation_canonical_from_jordan :
    (1 : M2) ∈ SquareCone ∧ (-1 : M2) ∉ SquareCone ∧ ∀ H : Herm2.Herm, NJr (-H) = NJr H :=
  ⟨one_mem_squareCone, neg_one_not_mem_squareCone, NJr_neg⟩

end Task7
