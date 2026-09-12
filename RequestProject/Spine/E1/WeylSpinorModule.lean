import Mathlib
import RequestProject.Spine.E1.Carrier
import RequestProject.Spine.E1.MatrixModel

/-!
# Spine / E1 : Clifford modules over the intrinsic carrier, and the Weyl module

This module contains the **algebraic** spinor-module material of the upstream experiment-1
Task-15 branch, and nothing else:

* `SpinCore.CliffordAction S` — a real module `S` with a real-linear action `c` of the
  carrier satisfying the Clifford relation `c(x)² = N(x) · id`.  Both the module and the
  action are *parameters*: no module is singled out by the carrier.
* `SpinCore.sig`, `SpinCore.sigBar` — the two conjugate half-spinor actions, given by the
  matrix pattern of `MatrixModel`, with `σ(x)·σ̄(x) = σ̄(x)·σ(x) = N(x)·1`.
* `SpinCore.WeylS := ℂ² × ℂ²`, `SpinCore.weylAct`, `SpinCore.weylAction` — a concrete
  Clifford action, so the parameter is inhabited (the branch is not vacuous).
* `SpinCore.weylChi`, `SpinCore.weyl_chirality` — the concrete module is `ℤ₂`-graded and the
  Clifford action is odd for that grading.  This is a property of the *chosen* module, not
  of the algebra.

**Import firewall.**  `Mathlib`, `Spine.E1.Carrier` and `Spine.E1.MatrixModel` only.  The
upstream Task-15 spinor file additionally imported the Maxwell/gauge-field branch and the
Hermitian carrier; neither is in the transitive closure of this module.  The first-order
(Dirac) operator, the dilation/mass-rescaling verdicts, the quantization, phase and
positive-frequency branches of the upstream development are **not** carried over: they are
recorded in `PROVENANCE_LEDGER.md` as excluded branches.

**Provenance.**  Upstream experiment 1, module `Task15Spinor`, sections "An abstract
Clifford action" and "A concrete Clifford action"; the statements are unchanged apart from
the carrier rename and the replacement of the Hermitian-layer matrix pattern by the
`MatrixModel` one.
-/

noncomputable section

namespace SpinCore

open Matrix

/-! ## An abstract Clifford action -/

/-- A module with an action of the carrier satisfying the Clifford relation for the
intrinsic quadratic form `N`.  Both the module and the action are *inputs*. -/
structure CliffordAction (S : Type) [NormedAddCommGroup S] [NormedSpace ℝ S] where
  /-- the action of a carrier vector -/
  act : LorentzCarrier → (S →L[ℝ] S)
  act_add : ∀ x y : LorentzCarrier, act (x + y) = act x + act y
  act_smul : ∀ (r : ℝ) (x : LorentzCarrier), act (r • x) = r • act x
  act_sq : ∀ (x : LorentzCarrier) (s : S), act x (act x s) = NS x • s

/-! ## The two half-spinor actions -/

/-- The half-spinor action `σ(x)`, the matrix pattern of `x`. -/
def sig (x : LorentzCarrier) : M2 := hMat x.1 (x.2 0) (x.2 1) (x.2 2)

/-- The conjugate half-spinor action `σ̄(x)`. -/
def sigBar (x : LorentzCarrier) : M2 := hMat x.1 (-(x.2 0)) (-(x.2 1)) (-(x.2 2))

theorem sig_mul_sigBar (x : LorentzCarrier) :
    sig x * sigBar x = ((NS x : ℝ) : ℂ) • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig, sigBar, hMat, Matrix.mul_apply, Fin.sum_univ_two, NS, sip,
      Complex.ext_iff, -Complex.ofReal_pow] <;> exact ⟨by ring, by ring⟩

theorem sigBar_mul_sig (x : LorentzCarrier) :
    sigBar x * sig x = ((NS x : ℝ) : ℂ) • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig, sigBar, hMat, Matrix.mul_apply, Fin.sum_univ_two, NS, sip,
      Complex.ext_iff, -Complex.ofReal_pow] <;> exact ⟨by ring, by ring⟩

theorem sig_add (x y : LorentzCarrier) : sig (x + y) = sig x + sig y := by
  simp only [sig, Prod.fst_add, Prod.snd_add, Pi.add_apply, hMat_add]

theorem sigBar_add (x y : LorentzCarrier) : sigBar (x + y) = sigBar x + sigBar y := by
  simp only [sigBar, Prod.fst_add, Prod.snd_add, Pi.add_apply, neg_add]
  rw [hMat_add]

theorem sig_smul (r : ℝ) (x : LorentzCarrier) : sig (r • x) = r • sig x := by
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hMat_smul]

theorem sigBar_smul (r : ℝ) (x : LorentzCarrier) : sigBar (r • x) = r • sigBar x := by
  simp only [sigBar, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [show -(r * x.2 0) = r * -(x.2 0) by ring, show -(r * x.2 1) = r * -(x.2 1) by ring,
    show -(r * x.2 2) = r * -(x.2 2) by ring, hMat_smul]

/-! ## The concrete Weyl module -/

/-- The concrete spinor module: a pair of two-component complex half-spinors. -/
abbrev WeylS : Type := (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- The Clifford action on `WeylS`, exchanging the two half-spinor sectors. -/
def weylMap (x : LorentzCarrier) : WeylS →ₗ[ℝ] WeylS where
  toFun p := (sig x *ᵥ p.2, sigBar x *ᵥ p.1)
  map_add' := by intro p q; simp [Matrix.mulVec_add]
  map_smul' := by
    intro r p
    simp [Matrix.mulVec_smul]

/-- The Clifford action as a continuous linear map. -/
def weylAct (x : LorentzCarrier) : WeylS →L[ℝ] WeylS := LinearMap.toContinuousLinearMap (weylMap x)

@[simp] theorem weylAct_apply (x : LorentzCarrier) (p : WeylS) :
    weylAct x p = (sig x *ᵥ p.2, sigBar x *ᵥ p.1) := rfl

/-- **The parameter is inhabited.**  A Clifford action on `ℂ² × ℂ²` exists. -/
def weylAction : CliffordAction WeylS where
  act := weylAct
  act_add := by
    intro x y
    apply ContinuousLinearMap.ext
    intro p
    simp [sig_add, sigBar_add, Matrix.add_mulVec]
  act_smul := by
    intro r x
    apply ContinuousLinearMap.ext
    intro p
    simp [sig_smul, sigBar_smul, Matrix.smul_mulVec]
  act_sq := by
    intro x p
    have h1 : sig x *ᵥ (sigBar x *ᵥ p.1) = NS x • p.1 := by
      rw [Matrix.mulVec_mulVec, sig_mul_sigBar, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Complex.coe_smul _ _
    have h2 : sigBar x *ᵥ (sig x *ᵥ p.2) = NS x • p.2 := by
      rw [Matrix.mulVec_mulVec, sigBar_mul_sig, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Complex.coe_smul _ _
    simp only [weylAct_apply]
    exact Prod.ext h1 h2

/-- The chirality involution of the concrete module. -/
def weylChi : WeylS →ₗ[ℝ] WeylS where
  toFun p := (p.1, -p.2)
  map_add' := by intro p q; simp; abel
  map_smul' := by intro r p; simp

/-- **Chirality.**  The Clifford action is odd for the grading of the concrete module: it
exchanges the two half-spinor sectors.  This is a property of the chosen module. -/
theorem weyl_chirality (x : LorentzCarrier) (p : WeylS) :
    weylChi (weylAct x p) = -(weylAct x (weylChi p)) := by
  simp [weylChi, weylAct_apply, Matrix.mulVec_neg]

end SpinCore
