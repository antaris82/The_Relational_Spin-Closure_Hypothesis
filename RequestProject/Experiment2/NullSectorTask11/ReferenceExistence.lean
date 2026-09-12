import RequestProject.Experiment2.NullSectorTask11.RelativeLiftRigidity
import RequestProject.Experiment2.NullSectorTask10.InternalLift

/-!
# Task 11, Layer 4: the existence witness (§15)

**This is the first module of Task 11 in which the explicit Task-10
representative enters.**  Everything in Layers 0–3 — in particular the exact
center theorem and the complete relative-lift rigidity theorem — was proved
without it, as demanded by §5 and §14.

The Task-10 element is imported under the neutral name `Uref`.  It is not called
a rotor, a spin lift or a unitary transformation.  Its only role is to turn the
*relative* classification into an *absolute* one.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-- **REFERENCE LIFT (neutral name).**  The Task-10 explicit internal lift. -/
noncomputable def Uref : ℝ → W := Ustd

theorem Uref_apply (θ : ℝ) :
    Uref θ = ksc (Real.cos (θ / 2)) (- Real.sin (θ / 2)) := rfl

/-- **DERIVED.**  The reference lift is a full-carrier lift in the sense of §7:
the Task-10 membership condition `U θ ∈ K` is simply dropped. -/
theorem Uref_isFullLift : IsFullLift Uref where
  unit := Ustd_isKLift.unit
  group := Ustd_isKLift.group
  conj := Ustd_isKLift.conj

/-- **DERIVED (§8).**  The reference lift is continuous. -/
theorem Uref_continuous : Continuous Uref := by
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [Uref, Ustd, ksc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1,
      wR] <;>
    fun_prop

/-- **DERIVED (§8).**  The reference lift is a continuous full lift. -/
theorem Uref_isContinuousFullLift : IsContinuousFullLift Uref where
  toIsFullLift := Uref_isFullLift
  cont := Uref_continuous

/-- The reference lift takes its values in the Task-10 two-plane `K`. -/
theorem Uref_mem_K (θ : ℝ) : Uref θ ∈ K := ksc_mem_K _ _

theorem Uref_ne_zero (θ : ℝ) : Uref θ ≠ 0 := Ustd_ne_zero θ

/-- **EXISTENCE (§15).**  A continuous full-carrier lift of the inherited
algebra action exists. -/
theorem exists_continuousFullLift : ∃ U : ℝ → W, IsContinuousFullLift U :=
  ⟨Uref, Uref_isContinuousFullLift⟩

end NullSectorTask11
