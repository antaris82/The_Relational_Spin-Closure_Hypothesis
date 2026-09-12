import Mathlib
import RequestProject.Experiment1.Task6Carrier
import RequestProject.Spine.Foundation.MinkowskiMatrix

/-!
# Task 6, Sections 6–7 : the positive cone *is* the future Minkowski cone

Section 6 identifies the intrinsic matrix-order cone with the coordinate future cone, and
Section 7 replaces the coordinate time-orientation condition `L₀₀ > 0` by intrinsic
future-cone preservation.
-/

noncomputable section

open Matrix Complex Mink4
open scoped ComplexOrder

namespace Carrier

/-! ## The quadratic form of a Hermitian matrix in coordinates -/

/-- The value of the Hermitian quadratic form `x ↦ x* H x` in real coordinates. -/
theorem quadForm_hMat (T X Y Z : ℝ) (x : Fin 2 → ℂ) :
    star x ⬝ᵥ (Herm2.hMat T X Y Z *ᵥ x) =
      (((T + Z) * ((x 0).re ^ 2 + (x 0).im ^ 2) + (T - Z) * ((x 1).re ^ 2 + (x 1).im ^ 2)
        + 2 * ((X * (x 0).re - Y * (x 0).im) * (x 1).re
             + (X * (x 0).im + Y * (x 0).re) * (x 1).im) : ℝ) : ℂ) := by
  simp [dotProduct, mulVec, Fin.sum_univ_two, Herm2.hMat, Complex.ext_iff, Pi.star_apply,
    ← Complex.ofReal_pow]
  constructor <;> ring

/-- The elementary real inequality behind positive semidefiniteness of a `2 × 2` Hermitian
matrix: `a, d ≥ 0` and `ad ≥ |z|²` imply the form is nonnegative. -/
theorem quad_nonneg {a d X Y p q r s : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (h : X ^ 2 + Y ^ 2 ≤ a * d) :
    0 ≤ a * (p ^ 2 + q ^ 2) + d * (r ^ 2 + s ^ 2)
        + 2 * ((X * p - Y * q) * r + (X * q + Y * p) * s) := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hXY : X ^ 2 + Y ^ 2 ≤ 0 := by rw [← ha0] at h; simpa using h
    have hX : X = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
    have hY : Y = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
    rw [← ha0, hX, hY]
    nlinarith [sq_nonneg r, sq_nonneg s]
  · nlinarith [sq_nonneg (a * p + X * r + Y * s), sq_nonneg (a * q + X * s - Y * r),
      sq_nonneg r, sq_nonneg s,
      mul_nonneg (sub_nonneg.2 h) (add_nonneg (sq_nonneg r) (sq_nonneg s))]

theorem quad_pos {a d X Y p q r s : ℝ} (ha : 0 < a) (h : X ^ 2 + Y ^ 2 < a * d)
    (hx : ¬ (p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0)) :
    0 < a * (p ^ 2 + q ^ 2) + d * (r ^ 2 + s ^ 2)
        + 2 * ((X * p - Y * q) * r + (X * q + Y * p) * s) := by
  have key : a * (a * (p ^ 2 + q ^ 2) + d * (r ^ 2 + s ^ 2)
        + 2 * ((X * p - Y * q) * r + (X * q + Y * p) * s))
      = (a * p + X * r + Y * s) ^ 2 + (a * q + X * s - Y * r) ^ 2
        + (a * d - X ^ 2 - Y ^ 2) * (r ^ 2 + s ^ 2) := by ring
  by_cases hrs : r = 0 ∧ s = 0
  · obtain ⟨hr, hs⟩ := hrs
    have hpq : ¬ (p = 0 ∧ q = 0) := by
      intro hc; exact hx ⟨hc.1, hc.2, hr, hs⟩
    have : 0 < p ^ 2 + q ^ 2 := by
      rcases not_and_or.1 hpq with h | h
      · have := lt_of_le_of_ne (sq_nonneg p) (Ne.symm (pow_ne_zero 2 h)); nlinarith [sq_nonneg q]
      · have := lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 h)); nlinarith [sq_nonneg p]
    rw [hr, hs]
    nlinarith
  · have hrs' : 0 < r ^ 2 + s ^ 2 := by
      rcases not_and_or.1 hrs with h | h
      · have := lt_of_le_of_ne (sq_nonneg r) (Ne.symm (pow_ne_zero 2 h)); nlinarith [sq_nonneg s]
      · have := lt_of_le_of_ne (sq_nonneg s) (Ne.symm (pow_ne_zero 2 h)); nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg (a * p + X * r + Y * s), sq_nonneg (a * q + X * s - Y * r),
      mul_pos (sub_pos.2 h) hrs']

/-! ## Section 6 : positive semidefinite = future causal cone -/

/-- **Section 6.** `H(T,X,Y,Z) ⪰ 0 ↔ T ≥ 0 ∧ T² - X² - Y² - Z² ≥ 0`. -/
theorem psd_iff_futureCone (T X Y Z : ℝ) :
    (Herm2.hMat T X Y Z).PosSemidef ↔ 0 ≤ T ∧ 0 ≤ T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := by
  constructor
  · intro h
    have hdet : (0 : ℂ) ≤ (Herm2.hMat T X Y Z).det := h.det_nonneg
    rw [Herm2.det_hMat] at hdet
    have hdet' : (0 : ℝ) ≤ T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := Complex.zero_le_real.1 hdet
    refine ⟨?_, hdet'⟩
    -- test vectors `e₀` and `e₁`
    have h1 := h.dotProduct_mulVec_nonneg ![1, 0]
    have h2 := h.dotProduct_mulVec_nonneg ![0, 1]
    rw [quadForm_hMat] at h1 h2
    simp at h1 h2
    have h1' : (0 : ℝ) ≤ T + Z := by
      have hc : (0 : ℂ) ≤ ((T + Z : ℝ) : ℂ) := by push_cast; exact h1
      exact Complex.zero_le_real.1 hc
    linarith
  · rintro ⟨hT, hQ⟩
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Herm2.hMat_isHermitian T X Y Z) ?_
    intro x
    rw [quadForm_hMat]
    have hTZ : 0 ≤ T + Z := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg (T - Z), sq_nonneg (T + Z)]
    have hTZ' : 0 ≤ T - Z := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg (T - Z), sq_nonneg (T + Z)]
    have hprod : X ^ 2 + Y ^ 2 ≤ (T + Z) * (T - Z) := by nlinarith
    have := quad_nonneg (a := T + Z) (d := T - Z) (X := X) (Y := Y)
      (p := (x 0).re) (q := (x 0).im) (r := (x 1).re) (s := (x 1).im) hTZ hTZ' hprod
    exact Complex.zero_le_real.2 this

/-- **Section 6.** `H(T,X,Y,Z) ≻ 0 ↔ T > 0 ∧ T² - X² - Y² - Z² > 0`. -/
theorem posDef_iff_futureTimelike (T X Y Z : ℝ) :
    (Herm2.hMat T X Y Z).PosDef ↔ 0 < T ∧ 0 < T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := by
  constructor
  · intro h
    have hdet : (0 : ℂ) < (Herm2.hMat T X Y Z).det := h.det_pos
    rw [Herm2.det_hMat] at hdet
    have hdet' : (0 : ℝ) < T ^ 2 - X ^ 2 - Y ^ 2 - Z ^ 2 := Complex.zero_lt_real.1 hdet
    refine ⟨?_, hdet'⟩
    have h1 := h.dotProduct_mulVec_pos (x := ![1, 0]) (by
      intro hc; have := congrFun hc 0; simp at this)
    have h2 := h.dotProduct_mulVec_pos (x := ![0, 1]) (by
      intro hc; have := congrFun hc 1; simp at this)
    rw [quadForm_hMat] at h1 h2
    simp at h1 h2
    have h1' : (0 : ℝ) < T + Z := by
      have hc : (0 : ℂ) < ((T + Z : ℝ) : ℂ) := by push_cast; exact h1
      exact Complex.zero_lt_real.1 hc
    linarith
  · rintro ⟨hT, hQ⟩
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (Herm2.hMat_isHermitian T X Y Z) ?_
    intro x hx
    rw [quadForm_hMat]
    have hTZ : 0 < T + Z := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg (T - Z), sq_nonneg (T + Z)]
    have hprod : X ^ 2 + Y ^ 2 < (T + Z) * (T - Z) := by nlinarith
    have hx' : ¬ ((x 0).re = 0 ∧ (x 0).im = 0 ∧ (x 1).re = 0 ∧ (x 1).im = 0) := by
      rintro ⟨a, b, c, d⟩
      apply hx
      funext i
      fin_cases i
      · simpa [Complex.ext_iff] using ⟨a, b⟩
      · simpa [Complex.ext_iff] using ⟨c, d⟩
    have := quad_pos (a := T + Z) (d := T - Z) (X := X) (Y := Y)
      (p := (x 0).re) (q := (x 0).im) (r := (x 1).re) (s := (x 1).im) hTZ hprod hx'
    exact Complex.zero_lt_real.2 this

/-- Coordinate-free packaging: the cone of the carrier in coordinates. -/
def FutureCone : Set (Fin 4 → ℝ) := {v | 0 ≤ v 0 ∧ 0 ≤ Q4 v}

/-- **Section 6, packaged.** Under the coordinate equivalence, the intrinsic positive
semidefinite cone is exactly the future causal cone. -/
theorem psdCone_eq_futureCone (v : Fin 4 → ℝ) :
    Herm2.hermCoordEquiv v ∈ PSDCone ↔ v ∈ FutureCone := by
  have : ((Herm2.hermCoordEquiv v : Herm2.Herm) : M2) = Herm2.hMat (v 0) (v 1) (v 2) (v 3) := rfl
  show ((Herm2.hermCoordEquiv v : Herm2.Herm) : M2).PosSemidef ↔ _
  rw [this, psd_iff_futureCone]
  simp [FutureCone, Q4]

/-! ## Section 7 : `L₀₀ > 0` is the coordinate expression of future-cone preservation -/

/-- Future-cone preservation, stated as "maps the cone into itself" (the weakest formulation
that turns out to be equivalent). -/
def PreservesFutureCone (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ v ∈ FutureCone, L *ᵥ v ∈ FutureCone

/-- **Section 7.** For a Lorentz transformation, the coordinate orthochronicity condition is
equivalent to intrinsic future-cone preservation. -/
theorem orthochronous_iff_preserves_futureCone {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : IsLorentz L) : 0 < L 0 0 ↔ PreservesFutureCone L := by
  constructor
  · intro h00 v hv
    obtain ⟨hv0, hvQ⟩ := hv
    refine ⟨?_, ?_⟩
    · have hrow := hL.row_zero_rel
      have hcs := cauchy3 (L 0 1) (L 0 2) (L 0 3) (v 1) (v 2) (v 3)
      have hexp : (L *ᵥ v) 0 = L 0 0 * v 0 + (L 0 1 * v 1 + L 0 2 * v 2 + L 0 3 * v 3) := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        ring
      rw [hexp]
      have hq : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ v 0 ^ 2 := by
        have : 0 ≤ v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := hvQ
        linarith
      have hp : 0 ≤ L 0 1 ^ 2 + L 0 2 ^ 2 + L 0 3 ^ 2 := by positivity
      by_contra hcon
      push_neg at hcon
      set S := L 0 1 * v 1 + L 0 2 * v 2 + L 0 3 * v 3 with hS
      have hSneg : S < -(L 0 0 * v 0) := by linarith
      have hav : 0 ≤ L 0 0 * v 0 := mul_nonneg (le_of_lt h00) hv0
      have hsq : (L 0 0 * v 0) ^ 2 < S ^ 2 := by nlinarith
      nlinarith [hcs, hrow, hq, sq_nonneg (v 0)]
    · rw [hL.preserves_Q4]
      exact hvQ
  · intro hpres
    have he0 : (![1, 0, 0, 0] : Fin 4 → ℝ) ∈ FutureCone := by
      constructor
      · norm_num
      · simp [Q4]
    have h := hpres _ he0
    have hval : (L *ᵥ ![1, 0, 0, 0]) 0 = L 0 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    have hnn : 0 ≤ L 0 0 := by rw [← hval]; exact h.1
    have hcol := hL.col_zero_rel
    have : 1 ≤ L 0 0 ^ 2 := by nlinarith [sq_nonneg (L 1 0), sq_nonneg (L 2 0), sq_nonneg (L 3 0)]
    rcases eq_or_lt_of_le hnn with h0 | h0
    · exfalso; rw [← h0] at this; norm_num at this
    · exact h0

/-- The cone is preserved *exactly* (not just mapped into itself) by an orthochronous Lorentz
transformation: its Lorentz inverse is orthochronous too. -/
theorem futureCone_image_eq {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) (h00 : 0 < L 0 0) :
    (fun v => L *ᵥ v) '' FutureCone = FutureCone := by
  have hinv : IsLorentz (J4 * Lᵀ * J4) := hL.of_inv
  have hinv00 : (J4 * Lᵀ * J4) 0 0 = L 0 0 := by
    simp [Matrix.mul_apply, J4, Matrix.diagonal_apply, Matrix.transpose_apply]
  have hpres := (orthochronous_iff_preserves_futureCone hL).1 h00
  have hpres' := (orthochronous_iff_preserves_futureCone hinv).1 (by rw [hinv00]; exact h00)
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hpres v hv
  · intro hw
    refine ⟨(J4 * Lᵀ * J4) *ᵥ w, hpres' w hw, ?_⟩
    show L *ᵥ ((J4 * Lᵀ * J4) *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, hL.inv_right, Matrix.one_mulVec]

end Carrier
