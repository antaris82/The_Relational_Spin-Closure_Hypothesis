import Mathlib
import RequestProject.Spine.E1.Hyperbolic
import RequestProject.Spine.E1.Coords

/-!
# Task 11, Phase I, obligation B2 : the shell branch without the Hermitian comparison leak

Task 10 proved transitivity of the intrinsic group `G_L` on the unit future shell `𝓗`
through two comparison-layer facts:

* `SpinCore.spatialRefl_det`, whose proof went through `Herm2`, `toHerm`,
  `hermCoordEquiv` and the Task-8 matrix reflection `Task8.reflY`;
* `SpinCore.det_sq_of_GLorWide`, whose proof transported the Task-9 wide-group determinant
  dichotomy across `spinHermConj`.

Both are replaced here by direct real proofs on `𝒮 = ℝ ⊕ ℝ³`
(`SpinCore.spatialReflI_det`, `SpinCore.det_sq_of_NS_preserving`), and the shell theorems are
rebuilt on them:

* `SpinCore.exists_GLor_map_oneI`;
* `SpinCore.shell_transitiveI`;
* `SpinCore.shell_eq_orbitI`.

This module imports `Task10Hyperbolic` and `Task11Coords` only; in particular it does not
import `Task10Shell`, `Task10Compare`, `Task10LieCompare`, `Herm2` proper, `Mink4` or
`SO13Plus`.  The Task-10 comparison-based proof is left untouched in `Task10Shell.lean`,
where it now serves only as an optional cross-check (`SpinCore.spatialRefl_det_crosscheck`
in `Task11Compare.lean`).
-/

noncomputable section

namespace SpinCore

open SpinCore Matrix

/-! ## B2.1 : the spatial reflection and its determinant, proved directly -/

/-- The intrinsic spatial reflection of the second `V`-coordinate.  Defined on the real
carrier only. -/
def spatialReflI : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier where
  toFun x := (x.1, ![x.2 0, -x.2 1, x.2 2])
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> simp [add_comm]
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> simp
  invFun x := (x.1, ![x.2 0, -x.2 1, x.2 2])
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> simp

@[simp] theorem spatialReflI_apply (x : LorentzCarrier) :
    spatialReflI x = (x.1, ![x.2 0, -x.2 1, x.2 2]) := rfl

theorem sip_spatialReflI (x y : LorentzCarrier) :
    sip (spatialReflI x).2 (spatialReflI y).2 = sip x.2 y.2 := by
  show sip ![x.2 0, -x.2 1, x.2 2] ![y.2 0, -y.2 1, y.2 2] = _
  simp [sip]

theorem spatialReflI_NS (x : LorentzCarrier) : NS (spatialReflI x) = NS x := by
  rw [NS_def, NS_def, sip_spatialReflI]
  rfl

theorem spatialReflI_wide : IsGLorWide spatialReflI := by
  refine ⟨spatialReflI_NS, fun x => ?_⟩
  rw [mem_coneS_iff, mem_coneS_iff, spatialReflI_NS]
  exact Iff.rfl

@[simp] theorem spatialReflI_one : spatialReflI sOne = sOne := by
  apply Prod.ext
  · rfl
  · funext i; fin_cases i <;> simp [sOne]

/-- The frame matrix of the spatial reflection. -/
theorem matOf_spatialReflI :
    matOf (spatialReflI : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
      = Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matOf_entry, uncoordFun, coordFun]

/-- **B2 (main).**  `det_ℝ(spatialRefl) = -1`, proved directly inside the real spin-factor
model.  No `Herm2`, no `toHerm`, no `hermCoordEquiv`, no Task-8 matrix comparison, no
complex matrices, no standard Lorentz matrices occur in the proof closure. -/
theorem spatialReflI_det : LinearMap.det (spatialReflI : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = -1 := by
  rw [← det_matOf, matOf_spatialReflI]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-! ## B2.2 : transitivity of `G_L` on the shell, rebuilt intrinsically -/

/-- **B2 (rebuilt).**  For every shell point there is a *proper* intrinsic automorphism
carrying the unit to it. -/
theorem exists_GLor_map_oneI {x : LorentzCarrier} (hx : x ∈ Shell) :
    ∃ F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier, F ∈ GLor ∧ F sOne = x := by
  have hB := boostEquiv_wide hx
  have hdet := det_sq_of_NS_preserving (F := boostEquiv hx) hB.1
  have hcases : LinearMap.det ((boostEquiv hx : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1 ∨
      LinearMap.det ((boostEquiv hx : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = -1 := by
    rcases mul_self_eq_one_iff.1 (by nlinarith [hdet] : LinearMap.det
      ((boostEquiv hx : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
      * LinearMap.det ((boostEquiv hx : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with h | h
  · exact ⟨boostEquiv hx, ⟨hB, h⟩, boostEquiv_one hx⟩
  · refine ⟨boostEquiv hx * spatialReflI, ⟨GLorWide.mul_mem hB spatialReflI_wide, ?_⟩, ?_⟩
    · have hcomp : ((boostEquiv hx * spatialReflI : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
          = ((boostEquiv hx : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
            ∘ₗ (spatialReflI : LorentzCarrier →ₗ[ℝ] LorentzCarrier) := rfl
      rw [hcomp, LinearMap.det_comp, h, spatialReflI_det]
      norm_num
    · show boostEquiv hx (spatialReflI sOne) = x
      rw [spatialReflI_one, boostEquiv_one]

/-- **B2 (rebuilt, K2).**  `G_L` acts transitively on the unit future shell, with a proof
whose dependency closure stays inside the intrinsic real branch. -/
theorem shell_transitiveI {x y : LorentzCarrier} (hx : x ∈ Shell) (hy : y ∈ Shell) :
    ∃ F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier, F ∈ GLor ∧ F x = y := by
  obtain ⟨Fx, hFx, hFx1⟩ := exists_GLor_map_oneI hx
  obtain ⟨Fy, hFy, hFy1⟩ := exists_GLor_map_oneI hy
  refine ⟨Fy * Fx⁻¹, GLor.mul_mem hFy (GLor.inv_mem hFx), ?_⟩
  show Fy (Fx⁻¹ x) = y
  have hone : Fx⁻¹ x = sOne := by
    rw [← hFx1]
    show (Fx⁻¹ * Fx) sOne = sOne
    rw [inv_mul_cancel]; rfl
  rw [hone, hFy1]

/-- **B2 (rebuilt).**  The shell is exactly the `G_L`-orbit of the unit. -/
theorem shell_eq_orbitI :
    Shell = {x : LorentzCarrier | ∃ F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier, F ∈ GLor ∧ F sOne = x} := by
  ext x
  constructor
  · intro hx
    exact exists_GLor_map_oneI hx
  · rintro ⟨F, hF, rfl⟩
    exact (GLor_shell hF sOne).1 one_mem_shell

end SpinCore
