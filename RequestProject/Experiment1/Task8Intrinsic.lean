import Mathlib
import RequestProject.Experiment1.Task7Cone
import RequestProject.Experiment1.Task7Jordan

/-!
# Task 8, Part A : intrinsic trace, quadratic norm and polarized form

This file builds the first half of the intrinsic chain

`(J, ∘, 1)  →  trJ  →  N_intr  →  B_intr`

on the real Jordan carrier `J = Herm₂(ℂ) = selfAdjoint M₂(ℂ)` with the Jordan product
`H ∘ K = ½(HK + KH)` (`Task7.jH`) and unit `Carrier.oneH`.

The *definitions* below mention only:

* the real vector space `Herm`;
* the Jordan product `Task7.jH` and its regular representation `Task7.jordanL`;
* `LinearMap.trace` over `ℝ` on a finite-dimensional real space.

In particular `trJ` does **not** mention `Matrix.trace`, `N_intr` does **not** mention
`Matrix.det`, and `B_intr` is the polarization of `N_intr`.

All statements comparing these objects with the standard matrix trace / determinant /
Minkowski form come *afterwards* and are labelled `STANDARD_IDENTIFICATION`.
-/

noncomputable section

open Matrix Complex Herm2

namespace Task8

open Task7 (jH jordanL jordanL_apply coe_jH NJr BJ trace_jordanL trace_from_jordan)

/-! ## A1 : the intrinsic Jordan trace -/

/-- **A1 (intrinsic definition).** The Jordan trace of `H` is half the real trace of the
Jordan regular representation `L_H : K ↦ H ∘ K`.  No matrix trace occurs. -/
def trJ (H : Herm) : ℝ := (LinearMap.trace ℝ Herm (jordanL H)) / 2

/-- The Jordan trace is real-linear in `H` (an immediate consequence of the definition and
the linearity of `H ↦ L_H`). -/
theorem trJ_add (H K : Herm) : trJ (H + K) = trJ H + trJ K := by
  have hL : jordanL (H + K) = jordanL H + jordanL K := by
    apply LinearMap.ext; intro L
    apply Subtype.ext
    show Carrier.jordan ((H : M2) + (K : M2)) (L : M2)
        = Carrier.jordan (H : M2) (L : M2) + Carrier.jordan (K : M2) (L : M2)
    simp only [Carrier.jordan, add_mul, mul_add]
    module
  rw [trJ, trJ, trJ, hL, map_add]
  ring

theorem trJ_smul (r : ℝ) (H : Herm) : trJ (r • H) = r * trJ H := by
  have hL : jordanL (r • H) = r • jordanL H := by
    apply LinearMap.ext; intro L
    apply Subtype.ext
    show Carrier.jordan (r • (H : M2)) (L : M2) = r • Carrier.jordan (H : M2) (L : M2)
    simp only [Carrier.jordan, Matrix.smul_mul, Matrix.mul_smul, smul_add]
    rw [smul_comm r ((2:ℂ)⁻¹) ((H : M2) * (L : M2)),
      smul_comm r ((2:ℂ)⁻¹) ((L : M2) * (H : M2))]
  rw [trJ, trJ, hL, map_smul]
  simp [mul_div_assoc]

/-- The Jordan trace in carrier coordinates: `trJ H = 2 T`. -/
theorem trJ_eq_coords (H : Herm) : trJ H = 2 * coordsOf (H : M2) 0 := by
  rw [trJ, trace_jordanL]; ring

@[simp] theorem trJ_hermCoordEquiv (v : Fin 4 → ℝ) : trJ (hermCoordEquiv v) = 2 * v 0 := by
  rw [trJ_eq_coords, hermCoordEquiv_apply, coordsOf_hMat]
  simp

/-- **A1 (STANDARD_IDENTIFICATION).** The intrinsic Jordan trace agrees with the ordinary
matrix trace.  This is a *comparison* theorem: the definition of `trJ` is independent of it. -/
theorem trJ_eq_matrix_trace (H : Herm) : trJ H = (Matrix.trace (H : M2)).re := by
  rw [trJ, trace_from_jordan]; ring

/-- The Jordan trace of the unit is `2`. -/
@[simp] theorem trJ_one : trJ Carrier.oneH = 2 := by
  rw [trJ_eq_matrix_trace]
  simp [Carrier.oneH, Matrix.trace]

/-! ## A2 : the intrinsic quadratic norm -/

/-- **A2 (intrinsic definition).** `N_intr(H) = ½ (trJ(H)² - trJ(H ∘ H))`.
No determinant occurs in this definition. -/
def Nintr (H : Herm) : ℝ := (trJ H ^ 2 - trJ (jH H H)) / 2

/-- The Jordan square in coordinates. -/
theorem jH_self_coords (v : Fin 4 → ℝ) :
    ((jH (hermCoordEquiv v) (hermCoordEquiv v) : Herm) : M2)
      = hMat (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) (2 * v 0 * v 1) (2 * v 0 * v 2)
          (2 * v 0 * v 3) := by
  rw [coe_jH, hermCoordEquiv_apply, Task7.hMat_jordan]
  congr 1 <;> ring

/-- `N_intr` in coordinates is the Minkowski quadratic form.  Proved directly from the
intrinsic definition. -/
@[simp] theorem Nintr_hermCoordEquiv (v : Fin 4 → ℝ) : Nintr (hermCoordEquiv v) = Qform v := by
  have h1 : trJ (jH (hermCoordEquiv v) (hermCoordEquiv v))
      = 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
    rw [trJ_eq_coords, jH_self_coords, coordsOf_hMat]
    simp
  rw [Nintr, h1, trJ_hermCoordEquiv, Qform]
  ring

/-- **A2 (STANDARD_IDENTIFICATION).** The intrinsic quadratic norm is the Task-7 norm
`N_J`, i.e. the real part of the matrix determinant. -/
theorem Nintr_eq_NJr (H : Herm) : Nintr H = NJr H := by
  obtain ⟨v, rfl⟩ : ∃ v, hermCoordEquiv v = H :=
    ⟨hermCoordEquiv.symm H, hermCoordEquiv.apply_symm_apply H⟩
  rw [Nintr_hermCoordEquiv, Task7.NJr_coords]

/-- **A2 (STANDARD_IDENTIFICATION).** `N_intr(H) = det H`. -/
theorem Nintr_eq_det (H : Herm) : ((Nintr H : ℝ) : ℂ) = ((H : M2)).det := by
  rw [Nintr_eq_NJr, NJr, Complex.ext_iff]
  refine ⟨by simp, by simp [Herm2.det_isReal_of_isHermitian
    ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)]⟩

/-! ## A3 : the intrinsic Cayley–Hamilton identity -/

/--
**A3.** `H ∘ H - trJ(H) H + N_intr(H) 1 = 0` in the Jordan carrier.

Proof dependency (documented): the identity is *stated* purely in Jordan data, but the
proof below goes through the ambient associative Cayley–Hamilton theorem
`Carrier.cayleyHamilton_two` for `M₂(ℂ)`; the Jordan square coincides with the associative
square (`Task7.jordan_self`), so no extra input is needed beyond that concrete model. -/
theorem jordan_cayleyHamilton_intr (H : Herm) :
    jH H H - trJ H • H + Nintr H • Carrier.oneH = 0 := by
  apply Subtype.ext
  show Carrier.jordan (H : M2) (H : M2) - (trJ H : ℝ) • (H : M2)
      + (Nintr H : ℝ) • ((1 : M2)) = (0 : M2)
  have hsq : Carrier.jordan (H : M2) (H : M2) = (H : M2) * (H : M2) := Task7.jordan_self _
  have hCH := Carrier.cayleyHamilton_two (H : M2)
  have htr : ((Matrix.trace (H : M2))) = ((trJ H : ℝ) : ℂ) := by
    have hre := Carrier.trace_isReal_of_isHermitian
      ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)
    have him : (Matrix.trace (H : M2)).im = 0 := Complex.conj_eq_iff_im.1 hre
    rw [trJ_eq_matrix_trace, Complex.ext_iff]
    exact ⟨by simp, by simp [him]⟩
  have hdet : ((H : M2)).det = ((Nintr H : ℝ) : ℂ) := (Nintr_eq_det H).symm
  rw [htr, hdet] at hCH
  have hs1 : ((trJ H : ℝ) • (H : M2)) = ((trJ H : ℝ) : ℂ) • (H : M2) := by
    ext i j; simp
  have hs2 : ((Nintr H : ℝ) • (1 : M2)) = ((Nintr H : ℝ) : ℂ) • (1 : M2) := by
    ext i j; simp
  rw [hsq, hs1, hs2]
  exact hCH

/-- **A3 (uniqueness of the quadratic coefficient).**  If `H ∘ H - trJ(H) H + r 1 = 0`
for a real scalar `r`, then `r = N_intr(H)`.  The identity therefore *characterizes* the
intrinsic norm. -/
theorem Nintr_unique_of_cayleyHamilton {H : Herm} {r : ℝ}
    (h : jH H H - trJ H • H + r • Carrier.oneH = 0) : r = Nintr H := by
  have h2 := jordan_cayleyHamilton_intr H
  have hcancel : r • Carrier.oneH = Nintr H • Carrier.oneH :=
    add_left_cancel (h.trans h2.symm)
  have hdiff : (r - Nintr H) • Carrier.oneH = (0 : Herm) := by
    rw [sub_smul, hcancel, sub_self]
  have hone : Carrier.oneH ≠ (0 : Herm) := by
    intro hz
    have hz' : ((Carrier.oneH : Herm) : M2) = 0 := congrArg Subtype.val hz
    exact one_ne_zero (show (1 : M2) = 0 from hz')
  rcases smul_eq_zero.1 hdiff with h' | h'
  · linarith [sub_eq_zero.1 h']
  · exact absurd h' hone

/-! ## A4 : the polarized bilinear form -/

/-- **A4 (intrinsic definition).** The polarization of the intrinsic norm. -/
def Bintr (H K : Herm) : ℝ := (Nintr (H + K) - Nintr H - Nintr K) / 2

theorem Bintr_eq_BJ (H K : Herm) : Bintr H K = BJ H K := by
  rw [Bintr, BJ, Nintr_eq_NJr, Nintr_eq_NJr, Nintr_eq_NJr]

@[simp] theorem Bintr_hermCoordEquiv (v w : Fin 4 → ℝ) :
    Bintr (hermCoordEquiv v) (hermCoordEquiv w) = Carrier.minkBilin v w := by
  rw [Bintr_eq_BJ, Task7.BJ_coords]

/-- **A4.** `B_intr(H,H) = N_intr(H)`. -/
theorem Bintr_self (H : Herm) : Bintr H H = Nintr H := by
  rw [Bintr_eq_BJ, Task7.BJ_self, Nintr_eq_NJr]

/-- **A4 (symmetry).** -/
theorem Bintr_symm (H K : Herm) : Bintr H K = Bintr K H := by
  rw [Bintr_eq_BJ, Bintr_eq_BJ, Task7.BJ_symm]

/-- **A4 (additivity, left).** -/
theorem Bintr_add_left (H H' K : Herm) : Bintr (H + H') K = Bintr H K + Bintr H' K := by
  simp only [Bintr_eq_BJ]; exact Task7.BJ_add_left H H' K

/-- **A4 (homogeneity, left).** -/
theorem Bintr_smul_left (r : ℝ) (H K : Herm) : Bintr (r • H) K = r * Bintr H K := by
  simp only [Bintr_eq_BJ]; exact Task7.BJ_smul_left r H K

/-- **A4 (additivity, right).** -/
theorem Bintr_add_right (H K K' : Herm) : Bintr H (K + K') = Bintr H K + Bintr H K' := by
  simp only [Bintr_eq_BJ]; exact Task7.BJ_add_right H K K'

/-- **A4 (homogeneity, right).** -/
theorem Bintr_smul_right (r : ℝ) (H K : Herm) : Bintr H (r • K) = r * Bintr H K := by
  simp only [Bintr_eq_BJ]; exact Task7.BJ_smul_right r H K

/-- **A4.** `B_intr` as a real bilinear map. -/
def BintrBilin : Herm →ₗ[ℝ] Herm →ₗ[ℝ] ℝ where
  toFun H :=
    { toFun := fun K => Bintr H K
      map_add' := by intro K K'; simpa using Bintr_add_right H K K'
      map_smul' := by intro r K; simpa using Bintr_smul_right r H K }
  map_add' H H' := by
    apply LinearMap.ext; intro K
    simpa using Bintr_add_left H H' K
  map_smul' r H := by
    apply LinearMap.ext; intro K
    simpa using Bintr_smul_left r H K

@[simp] theorem BintrBilin_apply (H K : Herm) : BintrBilin H K = Bintr H K := rfl

/-- **A4 (nondegeneracy).** -/
theorem Bintr_nondegenerate {H : Herm} (h : ∀ K, Bintr H K = 0) : H = 0 :=
  Task7.BJ_nondegenerate (fun K => by rw [← Bintr_eq_BJ]; exact h K)

/-! ### Signature -/

/-- **A4 (STANDARD_IDENTIFICATION).** In the standard coordinates
`H(T,X,Y,Z)` the intrinsic form is the Minkowski form. -/
theorem Bintr_coords (T X Y Z T' X' Y' Z' : ℝ) :
    Bintr (hermCoordEquiv ![T, X, Y, Z]) (hermCoordEquiv ![T', X', Y', Z'])
      = T * T' - X * X' - Y * Y' - Z * Z' := by
  rw [Bintr_hermCoordEquiv, Carrier.minkBilin_apply]
  simp

/-- **A4 (signature (1,3)).**  The Gram matrix of `B_intr` in the coordinate basis
`I, σ₁, σ₂, σ₃` is `diag(1,-1,-1,-1)`; this is a *theorem about the intrinsically defined
form*, not part of its definition. -/
theorem Bintr_gram (i j : Fin 4) :
    Bintr (Task7.basisElt i) (Task7.basisElt j) =
      if i = j then (if i = 0 then (1 : ℝ) else -1) else 0 := by
  rw [Bintr_eq_BJ]; exact Task7.BJ_gram i j

theorem Bintr_pos_on_unit : Bintr (Task7.basisElt 0) (Task7.basisElt 0) = 1 := by
  simpa using Bintr_gram 0 0

theorem Bintr_neg_on_space (i : Fin 4) (hi : i ≠ 0) :
    Bintr (Task7.basisElt i) (Task7.basisElt i) = -1 := by
  simpa [hi] using Bintr_gram i i

/-- Signature `(1,3)` in packaged form. -/
theorem Bintr_signature :
    Bintr (Task7.basisElt 0) (Task7.basisElt 0) = 1 ∧
    (∀ i : Fin 4, i ≠ 0 → Bintr (Task7.basisElt i) (Task7.basisElt i) = -1) ∧
    (∀ i j : Fin 4, i ≠ j → Bintr (Task7.basisElt i) (Task7.basisElt j) = 0) :=
  ⟨Bintr_pos_on_unit, Bintr_neg_on_space, fun i j hij => by
    rw [Bintr_gram]; simp [hij]⟩

end Task8
