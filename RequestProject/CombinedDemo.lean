import RequestProject.Spine.E1.Core
import RequestProject.Spine.E2.Core

/-!
# Combined smoke test for the refactored spine

This file witnesses that the two halves of the refactored proof spine — the intrinsic
Lorentz/Clifford/Spin core extracted from experiment 1
(`RequestProject.Spine.E1.*`, namespace `SpinCore`) and the family/lift/defect core
extracted from experiment 2 (`RequestProject.Spine.E2.*`) — coexist and are simultaneously
usable in one Lean environment.

It adds no mathematics: it forwards one already-proved result from each half.  There is no
cross-experiment bridge; the two halves remain mathematically independent.
-/

namespace CombinedDemo

/-- From the experiment-1 core: the intrinsic spin group of `Cl₃(ℝ)` covers the intrinsic
Lorentz group of the carrier, surjectively and with kernel exactly `{±1}`. -/
theorem spine_e1_spin_double_cover :
    (∀ {g : SpinCore.Cl3} (hg : SpinCore.IsSpinElem g), SpinCore.spinLorEquiv hg ∈ SpinCore.GLor) ∧
    (∀ F : SpinCore.LorentzCarrier ≃ₗ[ℝ] SpinCore.LorentzCarrier, F ∈ SpinCore.GLor →
      ∃ g : SpinCore.Cl3, ∃ hg : SpinCore.IsSpinElem g, SpinCore.spinLorEquiv hg = F) ∧
    (∀ {g : SpinCore.Cl3}, SpinCore.IsSpinElem g →
      ((∀ x, SpinCore.spinLor g x = x) ↔ g = 1 ∨ g = -1)) :=
  SpinCore.spin_double_cover_of_lorentz

/-- From the experiment-2 core: the family-level classification of liftability by
family-level kernel-defect neutrality, for an arbitrary internal projection `P` onto the
visible model group.  No concrete projection is fixed. -/
theorem spine_e2_family_classification
    {B : Type} [TopologicalSpace B] {E : B → Type} [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] (F : NullSectorTask32.BareMetricOrientedFamily B E)
    {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (P : NullSectorTask28.InternalProjection L NullSectorTask26.GvisModel) :
    NullSectorTask32.FamilyLiftable.{0, 0, 0} P F ↔
      NullSectorTask32.FamilyKernelDefectNeutral.{0, 0, 0} P F :=
  NullSectorTask32.familyLiftable_iff_familyKernelDefectNeutral P

end CombinedDemo

#print axioms CombinedDemo.spine_e1_spin_double_cover
#print axioms CombinedDemo.spine_e2_family_classification
