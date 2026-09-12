import Mathlib
import RequestProject.Experiment1.Task7Trace

/-!
# Task 7, Part A4 : the polarized quadratic form

`N_J` is the Cayley–Hamilton quadratic coefficient of Part A1, characterized there without
any group and computed in `Task7Trace.det_eq_trace_formula` from multiplication and trace
only.  Here it is polarized:

`B_J(H, K) = (N_J(H + K) - N_J(H) - N_J(K)) / 2`.

The *definition* of `B_J` uses no coordinates and no basis; only the proofs of the signature
statement do, as allowed.
-/

noncomputable section

open Matrix Complex Herm2

namespace Task7

/-- The real-valued quadratic norm on the Hermitian carrier: the Cayley–Hamilton quadratic
coefficient of Part A1, which equals the determinant (`NJ_eq_det`) and is computable from
multiplication and trace alone (`det_eq_trace_formula`). -/
def NJr (H : Herm2.Herm) : ℝ := ((H : Herm2.M2).det).re

/-- `N_J` is the unique Cayley–Hamilton coefficient, with no reference to the determinant
API: for a Hermitian `H`, `H² - (tr H) H + N_J(H) I = 0`. -/
theorem cayleyHamilton_NJr (H : Herm2.Herm) :
    (H : Herm2.M2) * (H : Herm2.M2) - (Matrix.trace (H : Herm2.M2)) • (H : Herm2.M2)
      + ((NJr H : ℝ) : ℂ) • (1 : Herm2.M2) = 0 := by
  have hdet : ((NJr H : ℝ) : ℂ) = (H : Herm2.M2).det := by
    have := Herm2.det_isReal_of_isHermitian
      ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)
    rw [NJr, Complex.ext_iff]
    simp [this]
  rw [hdet]
  exact Carrier.cayleyHamilton_two _

theorem NJr_coords (v : Fin 4 → ℝ) : NJr (hermCoordEquiv v) = Qform v := by
  rw [NJr, det_coords]
  simp

/-- The polarization of `N_J`.  Coordinate-free definition. -/
def BJ (H K : Herm2.Herm) : ℝ := (NJr (H + K) - NJr H - NJr K) / 2

/-- `B_J(H, H) = N_J(H)`. -/
theorem BJ_self (H : Herm2.Herm) : BJ H H = NJr H := by
  have h : NJr (H + H) = 4 * NJr H := by
    obtain ⟨v, rfl⟩ : ∃ v, hermCoordEquiv v = H :=
      ⟨hermCoordEquiv.symm H, hermCoordEquiv.apply_symm_apply H⟩
    rw [← map_add, NJr_coords, NJr_coords]
    simp [Qform, Pi.add_apply]
    ring
  rw [BJ, h]; ring

/-- `B_J` in coordinates is the Minkowski bilinear form. -/
theorem BJ_coords (v w : Fin 4 → ℝ) :
    BJ (hermCoordEquiv v) (hermCoordEquiv w) = Carrier.minkBilin v w := by
  rw [BJ, ← map_add, NJr_coords, NJr_coords, NJr_coords]
  simp [Qform, Pi.add_apply]
  ring

/-- The same statement for arbitrary carrier elements. -/
theorem BJ_eq_minkBilin (H K : Herm2.Herm) :
    BJ H K = Carrier.minkBilin (hermCoordEquiv.symm H) (hermCoordEquiv.symm K) := by
  have h1 : hermCoordEquiv (hermCoordEquiv.symm H) = H := hermCoordEquiv.apply_symm_apply H
  have h2 : hermCoordEquiv (hermCoordEquiv.symm K) = K := hermCoordEquiv.apply_symm_apply K
  calc BJ H K
      = BJ (hermCoordEquiv (hermCoordEquiv.symm H))
          (hermCoordEquiv (hermCoordEquiv.symm K)) := by rw [h1, h2]
    _ = Carrier.minkBilin (hermCoordEquiv.symm H) (hermCoordEquiv.symm K) := BJ_coords _ _

/-- **A4 (symmetry).** -/
theorem BJ_symm (H K : Herm2.Herm) : BJ H K = BJ K H := by
  rw [BJ_eq_minkBilin, BJ_eq_minkBilin, Carrier.minkBilin_symm]

/-- **A4 (additivity in the first slot).** -/
theorem BJ_add_left (H H' K : Herm2.Herm) : BJ (H + H') K = BJ H K + BJ H' K := by
  rw [BJ_eq_minkBilin, BJ_eq_minkBilin, BJ_eq_minkBilin, map_add]
  simp

/-- **A4 (homogeneity in the first slot).** -/
theorem BJ_smul_left (r : ℝ) (H K : Herm2.Herm) : BJ (r • H) K = r * BJ H K := by
  rw [BJ_eq_minkBilin, BJ_eq_minkBilin, map_smul]
  simp

theorem BJ_add_right (H K K' : Herm2.Herm) : BJ H (K + K') = BJ H K + BJ H K' := by
  rw [BJ_symm, BJ_add_left, BJ_symm H K, BJ_symm H K']

theorem BJ_smul_right (r : ℝ) (H K : Herm2.Herm) : BJ H (r • K) = r * BJ H K := by
  rw [BJ_symm, BJ_smul_left, BJ_symm H K]

/-- **A4 (bilinearity, bundled).** `B_J` as a genuine real bilinear map. -/
def BJbilin : Herm2.Herm →ₗ[ℝ] Herm2.Herm →ₗ[ℝ] ℝ where
  toFun H :=
    { toFun := fun K => BJ H K
      map_add' := BJ_add_right H
      map_smul' := by intro r K; simpa using BJ_smul_right r H K }
  map_add' H H' := by
    apply LinearMap.ext; intro K
    simpa using BJ_add_left H H' K
  map_smul' r H := by
    apply LinearMap.ext; intro K
    simpa using BJ_smul_left r H K

@[simp] theorem BJbilin_apply (H K : Herm2.Herm) : BJbilin H K = BJ H K := rfl

/-- **A4 (nondegeneracy).** -/
theorem BJ_nondegenerate {H : Herm2.Herm} (h : ∀ K, BJ H K = 0) : H = 0 := by
  set v := hermCoordEquiv.symm H with hv
  have hcoord : ∀ w : Fin 4 → ℝ, Carrier.minkBilin v w = 0 := by
    intro w
    have := h (hermCoordEquiv w)
    rwa [BJ_eq_minkBilin, ← hv, LinearEquiv.symm_apply_apply] at this
  have h0 := hcoord (Pi.single 0 1)
  have h1 := hcoord (Pi.single 1 1)
  have h2 := hcoord (Pi.single 2 1)
  have h3 := hcoord (Pi.single 3 1)
  simp [Carrier.minkBilin_apply] at h0 h1 h2 h3
  have hzero : v = 0 := by
    funext i
    fin_cases i <;> simpa using by first | exact h0 | exact h1 | exact h2 | exact h3
  have hH : H = hermCoordEquiv v := (hermCoordEquiv.apply_symm_apply H).symm
  rw [hH, hzero, map_zero]

/-! ### Signature `(1,3)` -/

/-- The four carrier basis elements `I, σ₁, σ₂, σ₃`, in coordinates. -/
def basisElt (i : Fin 4) : Herm2.Herm := hermCoordEquiv (Pi.single i 1)

/-- **A4 (signature).** The Gram matrix of `B_J` in the basis `I, σ₁, σ₂, σ₃` is
`diag(1, -1, -1, -1)`: the form has signature `(1,3)`. -/
theorem BJ_gram (i j : Fin 4) :
    BJ (basisElt i) (basisElt j) =
      if i = j then (if i = 0 then (1 : ℝ) else -1) else 0 := by
  rw [basisElt, basisElt, BJ_coords]
  fin_cases i <;> fin_cases j <;>
    simp [Carrier.minkBilin_apply]

/-- **A4 (signature, positive direction).** `B_J` is positive on the time axis. -/
theorem BJ_pos_on_unit : BJ (basisElt 0) (basisElt 0) = 1 := by
  simpa using BJ_gram 0 0

/-- **A4 (signature, negative directions).** `B_J` is negative on each space axis. -/
theorem BJ_neg_on_space (i : Fin 4) (hi : i ≠ 0) : BJ (basisElt i) (basisElt i) = -1 := by
  simpa [hi] using BJ_gram i i

end Task7
