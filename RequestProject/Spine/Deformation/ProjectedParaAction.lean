import RequestProject.Spine.Deformation.SharedTransport

/-!
# Task 38 / Part I : the explicit projected action of the shared transport state

**First module of the Task-38 fixed-base smoke test.**

Task 37 produced the shared native Spin-side transport state
`Task37.Deformation.transportState : ℝ → SpinGroup` and its projection
`Task37.Deformation.projectedTransportState l = spinCover (transportState l)`, and proved the
projection nontrivial for `l ≠ 0` by evaluating it on the intrinsic unit `1_𝒮` only.

Task 38 has to *solve* an intertwining equation whose unknown is a `C^∞` family of linear
automorphisms of the local model, so the partial evaluation is not enough: the **whole**
linear map has to be available in closed form, and it has to be visibly smooth in the
parameter.  This module supplies exactly that and nothing more:

```text
    paraMap l : LocalModel →L[ℝ] LocalModel
        = id + (cosh l - 1) • paraPlane + sinh l • paraSwap
    projectedTransportState_apply :  spinCover (transportState l) v = paraMap l v
```

`paraPlane` is the projector onto the `(scalar, e₀)` plane of the intrinsic carrier and
`paraSwap` exchanges its two coordinates; both are fixed, parameter-free continuous linear
maps of the project's own local model, so the whole parameter dependence sits in the two
real coefficients `cosh l - 1` and `sinh l`.  Smoothness in the parameter is then elementary
(`contDiff_paraMap`), and that is the only reason the closed form is computed here.

## Scope

Nothing in this module is a transport form, a parallel-transport operator or a loop
functional: `paraMap l` is the *value* of the already certified native projection
`SpinCore.spinCover` at the already certified one-parameter Spin state, written out in the
intrinsic coordinates of the carrier.  No new deformation source is introduced.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open SpinCore EmergentBase CliffordAlgebra

/-! ## Two fixed linear maps of the local model -/

/-- The projector of the local model onto the `(scalar, e₀)` plane of the intrinsic
carrier. -/
def paraPlane : LocalModel →L[ℝ] LocalModel :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)).prod
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (evec 0)).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))))

/-- The exchange of the two coordinates of the `(scalar, e₀)` plane. -/
def paraSwap : LocalModel →L[ℝ] LocalModel :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))).prod
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (evec 0)).comp
      (ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)))

@[simp] theorem paraPlane_fst (x : LocalModel) : (paraPlane x).1 = x.1 := rfl

@[simp] theorem paraPlane_snd (x : LocalModel) : (paraPlane x).2 = x.2 0 • evec 0 := rfl

@[simp] theorem paraSwap_fst (x : LocalModel) : (paraSwap x).1 = x.2 0 := rfl

@[simp] theorem paraSwap_snd (x : LocalModel) : (paraSwap x).2 = x.1 • evec 0 := rfl

/-! ## The closed form of the projected transport state -/

/-- **NEWLY DEFINED (Task 38).**  The closed form of the projected shared transport state as a
continuous linear map of the local model: the identity, corrected inside the `(scalar, e₀)`
plane by the two real coefficients `cosh l - 1` and `sinh l`. -/
def paraMap (l : ℝ) : LocalModel →L[ℝ] LocalModel :=
  ContinuousLinearMap.id ℝ LocalModel + (Real.cosh l - 1) • paraPlane + Real.sinh l • paraSwap

theorem paraMap_fst (l : ℝ) (x : LocalModel) :
    (paraMap l x).1 = Real.cosh l * x.1 + Real.sinh l * x.2 0 := by
  show x.1 + (Real.cosh l - 1) * x.1 + Real.sinh l * x.2 0 = _
  ring

theorem paraMap_snd (l : ℝ) (x : LocalModel) :
    (paraMap l x).2 = x.2 + (Real.cosh l - 1) • (x.2 0 • evec 0) + Real.sinh l • (x.1 • evec 0) :=
  rfl

theorem paraMap_zero : paraMap 0 = ContinuousLinearMap.id ℝ LocalModel := by
  unfold paraMap
  rw [Real.cosh_zero, Real.sinh_zero, sub_self, zero_smul, zero_smul, add_zero, add_zero]

/-- **DERIVED (Task 38).**  The closed form is `C^∞` in the parameter. -/
theorem contDiff_paraMap : ContDiff ℝ (⊤ : ℕ∞) (fun l : ℝ => paraMap l) := by
  refine ((contDiff_const.add ?_).add ?_)
  · exact (Real.contDiff_cosh.sub contDiff_const).smul contDiff_const
  · exact Real.contDiff_sinh.smul contDiff_const

/-! ## Identification with the native projection -/

private theorem cle_zero_anticomm {k : Fin 3} (hk : k ≠ 0) :
    cle 0 * cle k = -(cle k * cle 0) := by
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  rcases hk3 with rfl | rfl | rfl
  · exact absurd rfl hk
  · rw [t10, neg_neg]
  · rw [t20, neg_neg]

private theorem transportElem_conj_bar (l : ℝ) :
    (algebraMap ℝ Cl3 (Real.cosh (l / 2)) - Real.sinh (l / 2) • cle 0) * transportElem l = 1 := by
  unfold transportElem
  rw [sub_eq_add_neg, ← neg_smul, paravector_mul]
  have h1 : Real.cosh (l / 2) * Real.cosh (l / 2)
      + -Real.sinh (l / 2) * Real.sinh (l / 2) = 1 := by
    have h := Real.cosh_sq_sub_sinh_sq (l / 2)
    rw [pow_two, pow_two] at h
    rw [neg_mul, ← sub_eq_add_neg]
    exact h
  have h2 : Real.cosh (l / 2) * Real.sinh (l / 2)
      + -Real.sinh (l / 2) * Real.cosh (l / 2) = 0 := by ring
  rw [h1, h2, map_one, zero_smul, add_zero]

private theorem transportElem_mul_cle (l : ℝ) {k : Fin 3} (hk : k ≠ 0) :
    transportElem l * cle k * transportElem l = cle k := by
  have hmove : transportElem l * cle k
      = cle k * (algebraMap ℝ Cl3 (Real.cosh (l / 2)) - Real.sinh (l / 2) • cle 0) := by
    unfold transportElem
    rw [add_mul, mul_sub, Algebra.commutes, smul_mul_assoc, mul_smul_comm,
      cle_zero_anticomm hk, smul_neg]
    abel
  rw [hmove, mul_assoc, transportElem_conj_bar l, mul_one]

private theorem transportElem_mul_para (l : ℝ) (a p : ℝ) :
    transportElem l * (algebraMap ℝ Cl3 a + p • cle 0) * transportElem l
      = algebraMap ℝ Cl3 (Real.cosh l * a + Real.sinh l * p)
        + (Real.sinh l * a + Real.cosh l * p) • cle 0 := by
  have hc : Real.cosh l
      = Real.cosh (l / 2) * Real.cosh (l / 2) + Real.sinh (l / 2) * Real.sinh (l / 2) := by
    conv_lhs => rw [show l = 2 * (l / 2) by ring]
    rw [Real.cosh_two_mul, pow_two, pow_two]
  have hs : Real.sinh l
      = Real.cosh (l / 2) * Real.sinh (l / 2) + Real.sinh (l / 2) * Real.cosh (l / 2) := by
    conv_lhs => rw [show l = 2 * (l / 2) by ring]
    rw [Real.sinh_two_mul]
    ring
  unfold transportElem
  rw [paravector_mul, paravector_mul, hc, hs]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-- **DERIVED (Task 38), PRINCIPAL — the closed form is the native projection.**

The already certified projection `spinCover (transportState l)` of the shared native Spin-side
transport state acts on the local model exactly as `paraMap l`.  Nothing is postulated: the
identity is computed inside the project's own Clifford algebra from the definition of the
twisted action. -/
theorem projectedTransportState_apply (l : ℝ) (x : LocalModel) :
    ((projectedTransportState l : ↥GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) x
      = paraMap l x := by
  show spinLor (transportElem l) x = paraMap l x
  refine spinLor_unique ?_
  have hrev : CliffordAlgebra.reverse (Q := q3) (transportElem l) = transportElem l := by
    unfold transportElem cle
    rw [map_add, map_smul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse.commutes]
  have hsplit : ∀ y : LocalModel,
      spinToCl y = (algebraMap ℝ Cl3 y.1 + y.2 0 • cle 0) + (y.2 1 • cle 1 + y.2 2 • cle 2) := by
    intro y
    unfold spinToCl
    rw [ι_eq_sum]
    abel
  have h1 : transportElem l * (x.2 1 • cle 1) * transportElem l = x.2 1 • cle 1 := by
    rw [mul_smul_comm, smul_mul_assoc, transportElem_mul_cle l (by decide : (1 : Fin 3) ≠ 0)]
  have h2 : transportElem l * (x.2 2 • cle 2) * transportElem l = x.2 2 • cle 2 := by
    rw [mul_smul_comm, smul_mul_assoc, transportElem_mul_cle l (by decide : (2 : Fin 3) ≠ 0)]
  have hR : transportElem l * spinToCl x * transportElem l
      = algebraMap ℝ Cl3 (Real.cosh l * x.1 + Real.sinh l * x.2 0)
          + (Real.sinh l * x.1 + Real.cosh l * x.2 0) • cle 0
        + (x.2 1 • cle 1 + x.2 2 • cle 2) := by
    rw [hsplit x, show transportElem l * ((algebraMap ℝ Cl3 x.1 + x.2 0 • cle 0)
        + (x.2 1 • cle 1 + x.2 2 • cle 2)) * transportElem l
        = transportElem l * (algebraMap ℝ Cl3 x.1 + x.2 0 • cle 0) * transportElem l
          + transportElem l * (x.2 1 • cle 1 + x.2 2 • cle 2) * transportElem l from by
        rw [mul_add, add_mul], transportElem_mul_para l x.1 (x.2 0),
      show transportElem l * (x.2 1 • cle 1 + x.2 2 • cle 2) * transportElem l
        = transportElem l * (x.2 1 • cle 1) * transportElem l
          + transportElem l * (x.2 2 • cle 2) * transportElem l from by rw [mul_add, add_mul],
      h1, h2]
  have hfst : (paraMap l x).1 = Real.cosh l * x.1 + Real.sinh l * x.2 0 := paraMap_fst l x
  have hsnd0 : (paraMap l x).2 0 = Real.sinh l * x.1 + Real.cosh l * x.2 0 := by
    rw [paraMap_snd]
    show x.2 0 + (Real.cosh l - 1) * (x.2 0 * (if (0 : Fin 3) = 0 then 1 else 0))
        + Real.sinh l * (x.1 * (if (0 : Fin 3) = 0 then 1 else 0)) = _
    rw [if_pos rfl]
    ring
  have hsnd1 : (paraMap l x).2 1 = x.2 1 := by
    rw [paraMap_snd]
    show x.2 1 + (Real.cosh l - 1) * (x.2 0 * (if (1 : Fin 3) = 0 then 1 else 0))
        + Real.sinh l * (x.1 * (if (1 : Fin 3) = 0 then 1 else 0)) = _
    rw [if_neg (by decide : ¬ (1 : Fin 3) = 0)]
    ring
  have hsnd2 : (paraMap l x).2 2 = x.2 2 := by
    rw [paraMap_snd]
    show x.2 2 + (Real.cosh l - 1) * (x.2 0 * (if (2 : Fin 3) = 0 then 1 else 0))
        + Real.sinh l * (x.1 * (if (2 : Fin 3) = 0 then 1 else 0)) = _
    rw [if_neg (by decide : ¬ (2 : Fin 3) = 0)]
    ring
  rw [spinAct, hrev, hsplit (paraMap l x), hfst, hsnd0, hsnd1, hsnd2, hR]

/-! ## The parameter family of automorphisms -/

/-- **NEWLY DEFINED (Task 38).**  The closed form as a continuous linear *automorphism* of the
local model.  Invertibility is not assumed: the inverse is the closed form at the opposite
parameter, by the Task-37 one-parameter group law. -/
def paraEquiv (l : ℝ) : LocalModel ≃L[ℝ] LocalModel :=
  ContinuousLinearEquiv.equivOfInverse (paraMap l) (paraMap (-l))
    (fun x => by
      rw [← projectedTransportState_apply, ← projectedTransportState_apply,
        projectedTransportState, projectedTransportState, transportState_neg, map_inv]
      exact ((spinCover (transportState l) : ↥GLor) :
        LorentzCarrier ≃ₗ[ℝ] LorentzCarrier).symm_apply_apply x)
    (fun x => by
      rw [← projectedTransportState_apply, ← projectedTransportState_apply,
        projectedTransportState, projectedTransportState, transportState_neg, map_inv]
      exact ((spinCover (transportState l) : ↥GLor) :
        LorentzCarrier ≃ₗ[ℝ] LorentzCarrier).apply_symm_apply x)

@[simp] theorem paraEquiv_apply (l : ℝ) (x : LocalModel) : paraEquiv l x = paraMap l x := rfl

theorem paraEquiv_coe (l : ℝ) :
    ((paraEquiv l : LocalModel ≃L[ℝ] LocalModel) : LocalModel →L[ℝ] LocalModel) = paraMap l :=
  rfl

theorem paraEquiv_zero : paraEquiv 0 = ContinuousLinearEquiv.refl ℝ LocalModel := by
  refine ContinuousLinearEquiv.ext (funext fun x => ?_)
  show paraMap 0 x = x
  rw [paraMap_zero]
  rfl

/-- **DERIVED (Task 38).**  The closed forms compose additively in the parameter: this is the
Task-37 one-parameter group law read through the native projection. -/
theorem paraMap_add (a b : ℝ) (x : LocalModel) :
    paraMap (a + b) x = paraMap a (paraMap b x) := by
  rw [← projectedTransportState_apply, ← projectedTransportState_apply,
    ← projectedTransportState_apply, projectedTransportState, projectedTransportState,
    projectedTransportState, transportState_add, map_mul]
  rfl

/-- **DERIVED (Task 38).**  The projected transport state as an automorphism of the local
model, in the exact form the solder equation consumes. -/
theorem projectedTransportState_eq_paraEquiv (l : ℝ) :
    ((projectedTransportState l : ↥GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)
      = (paraEquiv l : LocalModel ≃ₗ[ℝ] LocalModel) :=
  LinearEquiv.ext (projectedTransportState_apply l)

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.paraMap
#print axioms Task37.Deformation.paraMap_zero
#print axioms Task37.Deformation.contDiff_paraMap
#print axioms Task37.Deformation.projectedTransportState_apply
#print axioms Task37.Deformation.paraEquiv
#print axioms Task37.Deformation.paraMap_add
#print axioms Task37.Deformation.projectedTransportState_eq_paraEquiv
