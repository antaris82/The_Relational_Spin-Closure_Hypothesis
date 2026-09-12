import Mathlib
import RequestProject.Spine.E1.Carrier

/-!
# Task 9, Part E : the real Clifford envelope of the spin factor

Everything in this file is defined over `ℝ` from the Euclidean data
`(V, ⟪·,·⟫) = (ℝ³, standard inner product)` only:

* `SpinCore.bil3` — the standard symmetric bilinear form on `ℝ³`;
* `SpinCore.q3` — the associated positive definite quadratic form `q(v) = ⟪v,v⟫`;
* `SpinCore.Cl3 = CliffordAlgebra q3` — the real Clifford algebra;
* `SpinCore.cle i = ι q3 (evec i)` — the images of the standard orthonormal basis;
* `SpinCore.omega = e₁e₂e₃` — the pseudoscalar.

Results:

* **E1** the symmetrized Clifford product on the embedded copy of `𝒮 = ℝ ⊕ ℝ³`
  reproduces the spin-factor Jordan product (`SpinCore.clifford_jordan`);
* **E2** the image of `ℝ ⊕ V` generates `Cl₃(ℝ)` as an `ℝ`-algebra
  (`SpinCore.adjoin_spinToCl_eq_top`);
* **E3** `ω² = -1` (`SpinCore.omega_sq`) and `ω` is central (`SpinCore.omega_central`);
* **E4** reversing the orientation of the orthonormal basis flips `ω`
  (`SpinCore.omega_swap01`);
* **G1/G2** the canonical reversion satisfies `reverse ω = -ω` (`SpinCore.reverse_omega`).

The exact centre `Z(Cl₃(ℝ)) = ℝ ⊕ ℝω ≅ ℂ` is proved in `Task9Pauli.lean`, after the
faithful Pauli representation is available.

**Audit.** No definition in this file mentions `ℂ`, `Matrix`, `det`, `PosSemidef` or any
Lorentz object; see `Task9Audit.lean` for the mechanical check.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-! ## The Euclidean data on `V = ℝ³` -/

/-- The standard symmetric bilinear form on `ℝ³`. -/
def bil3 : LinearMap.BilinMap ℝ (Fin 3 → ℝ) ℝ :=
  LinearMap.mk₂ ℝ (fun u v => u 0 * v 0 + u 1 * v 1 + u 2 * v 2)
    (by intros; simp [Pi.add_apply]; ring)
    (by intros; simp [Pi.smul_apply]; ring)
    (by intros; simp [Pi.add_apply]; ring)
    (by intros; simp [Pi.smul_apply]; ring)

@[simp] theorem bil3_apply (u v : Fin 3 → ℝ) : bil3 u v = sip u v := rfl

/-- The positive definite quadratic form `q(v) = ⟪v,v⟫` on `ℝ³`. -/
def q3 : QuadraticForm ℝ (Fin 3 → ℝ) := LinearMap.BilinMap.toQuadraticMap bil3

@[simp] theorem q3_apply (v : Fin 3 → ℝ) : q3 v = sip v v := rfl

theorem polar_q3 (u v : Fin 3 → ℝ) : QuadraticMap.polar q3 u v = 2 * sip u v := by
  simp [QuadraticMap.polar, q3, LinearMap.BilinMap.toQuadraticMap, bil3, sip]
  ring

/-- The real Clifford algebra of `(ℝ³, ⟪·,·⟫)`. -/
abbrev Cl3 : Type := CliffordAlgebra q3

/-- The image of the `i`-th standard basis vector of `ℝ³` in `Cl₃(ℝ)`. -/
def cle (i : Fin 3) : Cl3 := ι q3 (evec i)

/-! ## Clifford relations for the orthonormal basis -/

theorem cle_sq (i : Fin 3) : cle i * cle i = 1 := by
  rw [cle, ι_sq_scalar, q3_apply, sip_evec]
  simp

theorem cle_add_swap (i j : Fin 3) :
    cle i * cle j + cle j * cle i = algebraMap ℝ Cl3 (2 * sip (evec i) (evec j)) := by
  rw [cle, cle, ι_mul_ι_add_swap, polar_q3]

theorem cle_anticomm {i j : Fin 3} (h : i ≠ j) : cle i * cle j = -(cle j * cle i) := by
  have := cle_add_swap i j
  rw [sip_evec, if_neg h] at this
  simp only [mul_zero, map_zero] at this
  linear_combination (norm := noncomm_ring) this

/-- Every element of `V` is a real combination of the three basis vectors. -/
theorem ι_eq_sum (v : Fin 3 → ℝ) :
    ι q3 v = v 0 • cle 0 + v 1 • cle 1 + v 2 • cle 2 := by
  have hv : v = v 0 • evec 0 + v 1 • evec 1 + v 2 • evec 2 := by
    funext i
    fin_cases i <;> simp [evec, Pi.add_apply, Pi.smul_apply]
  rw [show ι q3 v = ι q3 (v 0 • evec 0 + v 1 • evec 1 + v 2 • evec 2) by rw [← hv]]
  simp [cle]

/-! ## E1 : the symmetrized Clifford product is the spin-factor Jordan product -/

/-- The embedding `𝒮 = ℝ ⊕ V → Cl₃(ℝ)`, `(a,v) ↦ a·1 + ι(v)`. -/
def spinToCl (x : LorentzCarrier) : Cl3 := algebraMap ℝ Cl3 x.1 + ι q3 x.2

@[simp] theorem spinToCl_apply (x : LorentzCarrier) :
    spinToCl x = algebraMap ℝ Cl3 x.1 + ι q3 x.2 := rfl

/-- Multiplication by a scalar from the left inside the Clifford algebra. -/
theorem algebraMap_mul_ι (r : ℝ) (w : Fin 3 → ℝ) :
    algebraMap ℝ Cl3 r * ι q3 w = r • ι q3 w := (Algebra.smul_def r _).symm

theorem ι_mul_algebraMap (r : ℝ) (w : Fin 3 → ℝ) :
    ι q3 w * algebraMap ℝ Cl3 r = r • ι q3 w := by
  rw [← Algebra.commutes, Algebra.smul_def]

/-- **E1 (symmetrized form).**  `xy + yx = 2 (x ∘ y)` on the embedded spin factor. -/
theorem spinToCl_symmetrized (x y : LorentzCarrier) :
    spinToCl x * spinToCl y + spinToCl y * spinToCl x = (2 : ℝ) • spinToCl (sJ x y) := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  have hswap : ι q3 u * ι q3 v + ι q3 v * ι q3 u = (2 * sip u v) • (1 : Cl3) := by
    rw [ι_mul_ι_add_swap, polar_q3, Algebra.algebraMap_eq_smul_one]
  have hsub : ι q3 u * ι q3 v = (2 * sip u v) • (1 : Cl3) - ι q3 v * ι q3 u := by
    rw [← hswap]; abel
  simp only [spinToCl_apply, sJ_fst, sJ_snd, add_mul, mul_add,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, map_add, map_smul, smul_add]
  rw [hsub]
  module

/-- **E1.**  On the embedded spin factor the symmetrized Clifford product is exactly the
spin-factor Jordan product:  `½(xy + yx) = x ∘ y`. -/
theorem clifford_jordan (x y : LorentzCarrier) :
    (2 : ℝ)⁻¹ • (spinToCl x * spinToCl y + spinToCl y * spinToCl x) = spinToCl (sJ x y) := by
  rw [spinToCl_symmetrized, smul_smul]
  norm_num

/-! ## E2 : the embedded spin factor generates the Clifford algebra -/

/-- **E2.**  The image of `ℝ ⊕ V` generates `Cl₃(ℝ)` as a real algebra. -/
theorem adjoin_spinToCl_eq_top :
    Algebra.adjoin ℝ (Set.range spinToCl) = ⊤ := by
  have hsub : Set.range (ι q3) ⊆ Set.range spinToCl := by
    rintro _ ⟨v, rfl⟩
    have h : spinToCl ((0 : ℝ), v) = ι q3 v := by
      rw [spinToCl_apply]
      rw [show ((0 : ℝ), v).1 = (0 : ℝ) from rfl, show ((0 : ℝ), v).2 = v from rfl,
        map_zero, zero_add]
    exact ⟨_, h⟩
  have := Algebra.adjoin_mono (R := ℝ) hsub
  rw [adjoin_range_ι] at this
  exact top_le_iff.1 this

/-! ## E3 : the pseudoscalar

We first install a small rewriting system that sorts words in the generators.
-/

theorem cle_swap_mul (i j : Fin 3) (h : i ≠ j) (x : Cl3) :
    cle i * (cle j * x) = -(cle j * (cle i * x)) := by
  rw [← mul_assoc, cle_anticomm h, neg_mul, mul_assoc]

theorem cle_sq_mul (i : Fin 3) (x : Cl3) : cle i * (cle i * x) = x := by
  rw [← mul_assoc, cle_sq, one_mul]

theorem s10 (x : Cl3) : cle 1 * (cle 0 * x) = -(cle 0 * (cle 1 * x)) :=
  cle_swap_mul 1 0 (by decide) x

theorem s20 (x : Cl3) : cle 2 * (cle 0 * x) = -(cle 0 * (cle 2 * x)) :=
  cle_swap_mul 2 0 (by decide) x

theorem s21 (x : Cl3) : cle 2 * (cle 1 * x) = -(cle 1 * (cle 2 * x)) :=
  cle_swap_mul 2 1 (by decide) x

theorem t10 : cle 1 * cle 0 = -(cle 0 * cle 1) := cle_anticomm (by decide)

theorem t20 : cle 2 * cle 0 = -(cle 0 * cle 2) := cle_anticomm (by decide)

theorem t21 : cle 2 * cle 1 = -(cle 1 * cle 2) := cle_anticomm (by decide)

/-- The pseudoscalar `ω = e₁e₂e₃` of the oriented orthonormal basis. -/
def omega : Cl3 := cle 0 * cle 1 * cle 2

theorem omega_assoc : omega = cle 0 * (cle 1 * cle 2) := by
  rw [omega, mul_assoc]

/-- **E3.** `ω² = -1`. -/
theorem omega_sq : omega * omega = -1 := by
  rw [omega_assoc]
  simp only [mul_assoc, s10, s20, s21, cle_sq, mul_neg, neg_neg,
    mul_one]

/-- The pseudoscalar commutes with each basis vector. -/
theorem omega_comm_cle (i : Fin 3) : omega * cle i = cle i * omega := by
  have h0 : omega * cle 0 = cle 0 * omega := by
    simp only [omega_assoc, mul_assoc, s10, t20, cle_sq_mul,
      mul_neg, neg_neg]
  have h1 : omega * cle 1 = cle 1 * omega := by
    simp only [omega_assoc, mul_assoc, s10, t21, cle_sq_mul,
      mul_neg]
  have h2 : omega * cle 2 = cle 2 * omega := by
    simp only [omega_assoc, mul_assoc, s20, s21, cle_sq,
      mul_neg, neg_neg, mul_one]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **E3 (centrality).**  `ω ∈ Z(Cl₃(ℝ))`. -/
theorem omega_central (x : Cl3) : omega * x = x * omega := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [Algebra.commutes]
  | ι v =>
      rw [ι_eq_sum]
      simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
        omega_comm_cle]
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

/-! ## E4 : orientation dependence -/

/-- **E4.**  Exchanging two basis vectors (i.e. reversing the orientation of the orthonormal
frame) replaces the pseudoscalar by its negative. -/
theorem omega_swap01 : cle 1 * cle 0 * cle 2 = -omega := by
  rw [mul_assoc, s10, omega_assoc]

/-! ## G1–G2 : reversion -/

/-- **G2.**  Clifford reversion negates the pseudoscalar. -/
theorem reverse_omega : reverse (Q := q3) omega = -omega := by
  have hrev : reverse (Q := q3) omega = cle 2 * (cle 1 * cle 0) := by
    rw [omega, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul]
    simp only [cle, reverse_ι]
  rw [hrev, omega_assoc]
  simp only [s20, t10, t21, mul_neg, neg_neg]

/-- Reversion fixes the embedded spin factor (scalars and vectors). -/
theorem reverse_spinToCl (x : LorentzCarrier) : reverse (Q := q3) (spinToCl x) = spinToCl x := by
  simp [spinToCl]

/-! ## I2 : the universal property (canonicity of the envelope from the quadratic data) -/

/-- **I2.**  Any real algebra `A` with a linear map `f : V → A` satisfying `f(v)² = q(v)·1`
receives a *unique* algebra map from `Cl₃(ℝ)` compatible with `ι`.  This is Mathlib's
universal property, recorded here as the precise sense in which the Clifford envelope is
canonical from the quadratic data alone. -/
theorem clifford_universal {A : Type} [Ring A] [Algebra ℝ A] (f : (Fin 3 → ℝ) →ₗ[ℝ] A)
    (hf : ∀ v, f v * f v = algebraMap ℝ A (q3 v)) :
    ∃! F : Cl3 →ₐ[ℝ] A, ∀ v, F (ι q3 v) = f v := by
  refine ⟨CliffordAlgebra.lift q3 ⟨f, hf⟩, fun v => CliffordAlgebra.lift_ι_apply f hf v, ?_⟩
  intro G hG
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  show G (ι q3 v) = CliffordAlgebra.lift q3 ⟨f, hf⟩ (ι q3 v)
  rw [hG v, CliffordAlgebra.lift_ι_apply]

end SpinCore
