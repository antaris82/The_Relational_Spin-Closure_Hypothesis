import Mathlib
import RequestProject.Experiment1.Task8Aut

/-!
# Task 9, Part A : freezing the Task-8 intrinsic Lorentz chain

This file contains **no new definitions**.  It re-exports, under stable Task-9 names, the
Task-8 theorems that constitute the accepted intrinsic layer

`(J, ∘, 1) → tr_J → N_intr → B_intr`,  `(J, ∘, 1) → 𝒞_J`,
`(N_intr, 𝒞_J, orientation) → JordanConeAut`,

together with the *standard identifications* that are allowed to occur only afterwards:

`N_intr = det`, `𝒞_J = PSD`, `B_intr = Minkowski bilinear form`,
`JordanConeAut ≅ SO⁺(1,3)`.

No later Task-9 file redefines any of these objects; every new Task-9 construction
(spin factor, Clifford envelope, Pauli representation) is compared with this frozen layer,
never used to alter it.
-/

noncomputable section

open Matrix Herm2
open scoped ComplexOrder

namespace Task9

/-! ## A1 : the frozen intrinsic definitions (references only) -/

/-- The frozen intrinsic Jordan trace (Task 8). -/
theorem frozen_trJ_def (H : Herm) :
    Task8.trJ H = (LinearMap.trace ℝ Herm (Task7.jordanL H)) / 2 := rfl

/-- The frozen intrinsic quadratic norm (Task 8). -/
theorem frozen_Nintr_def (H : Herm) :
    Task8.Nintr H = (Task8.trJ H ^ 2 - Task8.trJ (Task7.jH H H)) / 2 := rfl

/-- The frozen intrinsic polarized form (Task 8). -/
theorem frozen_Bintr_def (H K : Herm) :
    Task8.Bintr H K = (Task8.Nintr (H + K) - Task8.Nintr H - Task8.Nintr K) / 2 := rfl

/-- The frozen intrinsic square cone (Task 8). -/
theorem frozen_ConeJ_def : Task8.ConeJ = {H : Herm | ∃ X : Herm, H = Task7.jH X X} := rfl

/-! ## A2 : the frozen standard identifications -/

/-- `N_intr = det` (frozen Task-8 comparison theorem). -/
theorem frozen_Nintr_eq_det (H : Herm) : ((Task8.Nintr H : ℝ) : ℂ) = ((H : M2)).det :=
  Task8.Nintr_eq_det H

/-- `𝒞_J = PSD` (frozen Task-8 comparison theorem). -/
theorem frozen_coneJ_eq_psd : Task8.ConeJ = {H : Herm | ((H : M2)).PosSemidef} :=
  Task8.coneJ_eq_psd

/-- `B_intr` is the Minkowski bilinear form in the standard coordinates
(frozen Task-8 comparison theorem). -/
theorem frozen_Bintr_minkowski (T X Y Z T' X' Y' Z' : ℝ) :
    Task8.Bintr (hermCoordEquiv ![T, X, Y, Z]) (hermCoordEquiv ![T', X', Y', Z'])
      = T * T' - X * X' - Y * Y' - Z * Z' :=
  Task8.Bintr_coords T X Y Z T' X' Y' Z'

/-- Signature `(1,3)` of the intrinsic form (frozen). -/
theorem frozen_Bintr_signature :
    Task8.Bintr (Task7.basisElt 0) (Task7.basisElt 0) = 1 ∧
    (∀ i : Fin 4, i ≠ 0 → Task8.Bintr (Task7.basisElt i) (Task7.basisElt i) = -1) ∧
    (∀ i j : Fin 4, i ≠ j → Task8.Bintr (Task7.basisElt i) (Task7.basisElt j) = 0) :=
  Task8.Bintr_signature

/-- `JordanConeAut ≅ SO⁺(1,3)` (frozen Task-8 classification). -/
def frozen_jordanConeAut_SO13Plus : Task8.JordanConeAut ≃* Mink4.SO13Plus :=
  Task8.jordanConeAut_mulEquiv_SO13Plus

/-- The frozen intrinsic chain, packaged. -/
theorem frozen_chain :
    (∀ H : Herm, Task8.Nintr H = (Task8.trJ H ^ 2 - Task8.trJ (Task7.jH H H)) / 2) ∧
    (∀ H K : Herm, Task8.Bintr H K = (Task8.Nintr (H + K) - Task8.Nintr H - Task8.Nintr K) / 2) ∧
    Task8.ConeJ = {H : Herm | ∃ X : Herm, H = Task7.jH X X} ∧
    (∀ H : Herm, ((Task8.Nintr H : ℝ) : ℂ) = ((H : M2)).det) ∧
    Task8.ConeJ = {H : Herm | ((H : M2)).PosSemidef} ∧
    Nonempty (Task8.JordanConeAut ≃* Mink4.SO13Plus) :=
  ⟨frozen_Nintr_def, frozen_Bintr_def, frozen_ConeJ_def, frozen_Nintr_eq_det,
    frozen_coneJ_eq_psd, ⟨frozen_jordanConeAut_SO13Plus⟩⟩

end Task9
