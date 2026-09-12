import Mathlib
import RequestProject.Experiment1.SpinSurjectivity
import RequestProject.Experiment1.SectorLorentzGroup

/-!
# Section 19 : the `1+1` split construction as the exact diagonal restriction

This file proves that the previously formalized `1+1` split-sector construction
(`Sector.SectorAlgebra`, its positive norm-one group and the independently defined
`Lorentz.SO11Plus`) is the *diagonal / longitudinal restriction* of the `3+1` Hermitian
`SL(2, ℂ)` representation:

* `SpinLorentz.diagonal_boost` — `A_η D(u,v) A_ηᴴ = D(e^η u, e^{-η} v)`;
* `SpinLorentz.diagonal_boost_TZ` — the same in `(T, Z)` coordinates, giving the standard
  `1+1` boost with `X, Y` fixed;
* `SpinLorentz.sectorEmb` — the injective algebra embedding of the abstract split carrier into
  `M₂(ℂ)` by diagonal matrices, sending `p ↦ P`, `q ↦ Q`, `ε ↦ σ₃`, `N ↦ det`;
* `SpinLorentz.v3_diagonal_restriction` — for every element of the `1+1` positive norm-one
  group there is an element of `SL(2, ℂ)` whose congruence action restricts on the diagonal
  sector to multiplication by it, and whose `4 × 4` Lorentz matrix restricts on the
  longitudinal plane to the corresponding element of `SO₀(1,1)`.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-! ## The diagonal congruence action -/

/-- **Section 19.** The diagonal boost acts on the diagonal sector reciprocally. -/
theorem diagonal_boost (η u v : ℝ) :
    ((boostLift η : SL2C) : M2) * Herm2.D u v * ((boostLift η : SL2C) : M2)ᴴ
      = Herm2.D (Real.exp η * u) (Real.exp (-η) * v) := by
  have h1 : ((Real.exp (η/2) : ℝ) : ℂ) * ((Real.exp (η/2) : ℝ) : ℂ) = ((Real.exp η : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  have h2 : ((Real.exp (-η/2) : ℝ) : ℂ) * ((Real.exp (-η/2) : ℝ) : ℂ)
      = ((Real.exp (-η) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostLift, Herm2.D, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      -Complex.ofReal_exp]
  · linear_combination (u : ℂ) * h1
  · linear_combination (v : ℂ) * h2

/-- **Section 19.** In `(T, Z)` coordinates the diagonal congruence action is the standard
`1+1` boost, with the two transverse coordinates untouched. -/
theorem diagonal_boost_TZ (η T Z : ℝ) :
    ((boostLift η : SL2C) : M2) * Herm2.hMat T 0 0 Z * ((boostLift η : SL2C) : M2)ᴴ
      = Herm2.hMat (Real.cosh η * T + Real.sinh η * Z) 0 0
          (Real.sinh η * T + Real.cosh η * Z) := by
  rw [← Herm2.D_eq_hMat, diagonal_boost, ← Herm2.D_eq_hMat]
  have hc : Real.cosh η = (Real.exp η + Real.exp (-η)) / 2 := Real.cosh_eq η
  have hs : Real.sinh η = (Real.exp η - Real.exp (-η)) / 2 := Real.sinh_eq η
  congr 1 <;> rw [hc, hs] <;> ring

/-! ## The longitudinal restriction of the `4 × 4` representation -/

/-- The longitudinal inclusion `ℝ² ↪ ℝ⁴`, `(T, Z) ↦ (T, 0, 0, Z)`. -/
def longIncl (v : Fin 2 → ℝ) : Fin 4 → ℝ := ![v 0, 0, 0, v 1]

/-- **Section 19.** On the longitudinal plane the `3+1` representation of the diagonal boost
subgroup is exactly the `1+1` boost matrix `B η` of the previous construction. -/
theorem rep_boostLift_long (η : ℝ) (v : Fin 2 → ℝ) :
    rep (boostLift η) *ᵥ longIncl v = longIncl (Lorentz.B η *ᵥ v) := by
  rw [rep_boostLift]
  ext i
  fin_cases i <;>
    simp [longIncl, boostZ, Lorentz.B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **Section 19.** The two transverse coordinates are fixed by the diagonal boost. -/
theorem rep_boostLift_transverse (η : ℝ) (v : Fin 4 → ℝ) :
    (rep (boostLift η) *ᵥ v) 1 = v 1 ∧ (rep (boostLift η) *ᵥ v) 2 = v 2 := by
  rw [rep_boostLift]
  constructor <;>
    simp [boostZ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! ## The abstract `1+1` split carrier inside `M₂(ℂ)` -/

variable {𝔸 : Type*} [CommRing 𝔸] [Algebra ℝ 𝔸] (S : Sector.SectorAlgebra 𝔸)

/-- **Section 4/19.** The abstract split carrier embeds into `M₂(ℂ)` as the diagonal
subalgebra. -/
def sectorEmb : 𝔸 →ₐ[ℝ] M2 := Herm2.diagEmb.comp (S.equivProd : 𝔸 →ₐ[ℝ] ℝ × ℝ)

theorem sectorEmb_apply (x : 𝔸) : sectorEmb S x = Herm2.D (S.coordP x) (S.coordQ x) := rfl

theorem sectorEmb_injective : Function.Injective (sectorEmb S) := by
  intro x y h
  exact S.equivProd.injective (Herm2.diagEmb_injective h)

theorem sectorEmb_p : sectorEmb S S.p = Herm2.PP := by
  rw [sectorEmb_apply, S.coordP_p, S.coordQ_p]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Herm2.D, Herm2.PP]

theorem sectorEmb_q : sectorEmb S S.q = Herm2.PM := by
  rw [sectorEmb_apply, S.coordP_q, S.coordQ_q]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Herm2.D, Herm2.PM]

/-- **Section 5/19.** The split generator `ε = p - q` is represented by `σ₃`. -/
theorem sectorEmb_epsilon : sectorEmb S S.epsilon = Herm2.sigma3 := by
  rw [Sector.SectorAlgebra.epsilon, map_sub, sectorEmb_p, sectorEmb_q,
    Herm2.sigma3_eq_PP_sub_PM]

/-- **Section 19.** The split norm is carried to the determinant. -/
theorem det_sectorEmb (x : 𝔸) : (sectorEmb S x).det = ((S.N x : ℝ) : ℂ) := by
  rw [sectorEmb_apply, Herm2.det_D]
  rfl

/-- **Section 19.** The `1+1` action (multiplication by `g η`) is the restriction of the
`3+1` congruence action by `A_η ∈ SL(2, ℂ)`. -/
theorem sectorEmb_congr_boost (η : ℝ) (x : 𝔸) :
    ((boostLift η : SL2C) : M2) * sectorEmb S x * ((boostLift η : SL2C) : M2)ᴴ
      = sectorEmb S (S.gElem η * x) := by
  rw [sectorEmb_apply, diagonal_boost, sectorEmb_apply, S.coordP_gElem_mul, S.coordQ_gElem_mul]

/-- **Section 19, main restriction theorem.** For every element `u` of the `1+1` positive
norm-one group there is `A ∈ SL(2, ℂ)` such that

* the congruence action of `A` restricted to the diagonal split carrier is exactly
  multiplication by `u`, and
* the induced real `4 × 4` Lorentz transformation restricted to the longitudinal plane is
  exactly the element of the independently defined `SO₀(1,1)` corresponding to `u`.

Thus the previously verified `1+1` construction is an exact substructure of the `3+1`
Hermitian `SL(2, ℂ)` representation. -/
theorem v3_diagonal_restriction (u : S.U1posUnits) :
    ∃ A : SL2C,
      (∀ x : 𝔸, (A : M2) * sectorEmb S x * (A : M2)ᴴ = sectorEmb S (((u : 𝔸ˣ) : 𝔸) * x)) ∧
      (∀ v : Fin 2 → ℝ, rep A *ᵥ longIncl v
        = longIncl (((S.positiveNormOne_mulEquiv_SO11Plus u :
            Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v)) := by
  obtain ⟨η, hη, -⟩ := S.exists_unique_eta_units u
  refine ⟨boostLift η, fun x => ?_, fun v => ?_⟩
  · rw [hη]
    exact sectorEmb_congr_boost S η x
  · rw [rep_boostLift_long, S.Phi_coe_eq_regMatrix u, hη,
      S.regularAction_matrix_eq_lorentzBoost]

end SpinLorentz
