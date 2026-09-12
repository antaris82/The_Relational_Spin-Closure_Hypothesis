import RequestProject.Spine.Solder.RegularSolder

/-!
# Task 37 / Part II : the single shared native Spin-side transport source

**First module of the Task-37 deformation-preparation branch.**

Task 37 does **not** perform any deformation experiment.  It prepares the interface in which
the next task can ask a single question:

```text
    λ  ⟶  shared native Spin-side deformation
       ⟶  projected Lorentz transport (derived, never independently chosen)
       ⟶  global gluing + regular solder closure
       ⟶  EXISTS / DOES NOT EXIST
```

## What "transport" means here — exactly

The audit of the frozen source (see `TASK37_DEFORMATION_INTERFACE.md`) gives the following
picture, and it must not be blurred:

```text
native Spin transition cocycle   Spine.SpinNative.TransitionData   VARIABLE (primitive)
projected Lorentz cocycle        Spine.SpinNative.Projection       DERIVED (spinCover)
projected Lorentz transition     Spine.Solder.InternalLorentz      DERIVED
tangent coordinate transition Dφ Spine.Emergent.TangentTransition  DERIVED from the gluing
regular solder comparison A      Spine.Solder.RegularSolder        VARIABLE (extra datum)
Spin/Lorentz connection form     —                                 NOT FORMALIZED
Spin/Lorentz holonomy            —                                 NOT FORMALIZED
```

**CONNECTION / PARALLEL-TRANSPORT-FORM / LOOP-TRANSPORT DEFORMATION: NOT YET FORMALIZED.**
The project contains no differential-form transport datum and no loop-transport datum at all,
so the strongest transport object currently available is the *native Spin transition cocycle*
together with the group element it takes on an overlap.  The deformation interface is prepared
exactly there, and nothing is pretended beyond it.

## The deformation source

The single deformation source offered to the next task is a one-parameter family of elements
of the project's own intrinsic Spin group,

```text
    transportState : ℝ → SpinCore.SpinGroup ,      transportState 0 = 1 ,
    transportState (a + b) = transportState a * transportState b .
```

It is built inside the project's own Clifford algebra `SpinCore.Cl3` from the explicit
paravector generator `SpinCore.cle 0` — no external group, no matrix model, no exponential
map, no chart-dependent input.  Its projection to the intrinsic Lorentz group is
`SpinCore.spinCover (transportState l)`, and **that is the only way** a Lorentz-side datum may
enter the deformation branch: the Lorentz side is a function of the Spin side, never a second
adjustable field (`Task37.Deformation.projected_determined_by_spin`).

`λ : ℝ` is a genuine finite real parameter with the distinguished neutral value `λ = 0`.
Extended reals are **not** used as group parameters: `λ → 0±` and `λ → ±∞` are limit regimes
for the next task, not elements of any transition system.

## Anti-target-leakage (Task 37 §12)

Nothing in this branch mentions, assumes or selects a curvature sign, a sectional curvature, a
value `κ = +1, 0, −1`, a sphere, hyperbolic space, de Sitter, anti-de Sitter, Minkowski as a
requested output, an Einstein equation or a cosmological constant.  The parameter `λ` is a
transport-side deformation parameter and nothing else; whether *any* geometric pattern follows
from it is precisely the open question handed to Task 38.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

/-! ## The shared native Spin-side transport state -/

/-- **NEWLY DEFINED (Task 37).**  The Clifford-algebra element underlying the shared native
Spin-side transport state: the paravector combination
`cosh (λ/2) + sinh (λ/2) · e₀` in the project's own algebra `SpinCore.Cl3`. -/
def transportElem (l : ℝ) : Cl3 :=
  algebraMap ℝ Cl3 (Real.cosh (l / 2)) + Real.sinh (l / 2) • cle 0

/-- **DERIVED (Task 37).**  The Clifford conjugate flips the sign of the paravector part. -/
theorem cconj_transportElem (l : ℝ) :
    cconj (transportElem l)
      = algebraMap ℝ Cl3 (Real.cosh (l / 2)) - Real.sinh (l / 2) • cle 0 := by
  unfold cconj transportElem cle
  rw [map_add, map_add, map_smul, map_smul, CliffordAlgebra.reverse_ι,
    CliffordAlgebra.involute_ι, CliffordAlgebra.reverse.commutes, AlgHom.commutes, smul_neg]
  exact (sub_eq_add_neg _ _).symm

/-- **DERIVED (Task 37).**  The product law of the scalar/`e₀` paravector plane.  This is the
only algebraic computation the deformation source needs. -/
theorem paravector_mul (a b c d : ℝ) :
    (algebraMap ℝ Cl3 a + b • cle 0) * (algebraMap ℝ Cl3 c + d • cle 0)
      = algebraMap ℝ Cl3 (a * c + b * d) + (a * d + b * c) • cle 0 := by
  have h1 : algebraMap ℝ Cl3 a * algebraMap ℝ Cl3 c = algebraMap ℝ Cl3 (a * c) :=
    (map_mul _ _ _).symm
  have h2 : algebraMap ℝ Cl3 a * (d • cle 0) = (a * d) • cle 0 := by
    rw [mul_smul_comm, Algebra.smul_def, ← mul_assoc, ← map_mul, ← Algebra.smul_def,
      mul_comm d a]
  have h3 : (b • cle 0) * algebraMap ℝ Cl3 c = (b * c) • cle 0 := by
    rw [smul_mul_assoc, ← Algebra.commutes c (cle 0), Algebra.smul_def, ← mul_assoc,
      ← map_mul, ← Algebra.smul_def]
  have h4 : (b • cle 0) * (d • cle 0) = algebraMap ℝ Cl3 (b * d) := by
    rw [smul_mul_smul_comm, cle_sq]
    exact (Algebra.algebraMap_eq_smul_one (b * d)).symm
  rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, map_add, add_smul]
  abel

/-- **DERIVED (Task 37).**  The transport element is a genuine element of the intrinsic Spin
group: `g · cconj g = cconj g · g = 1`, by `cosh² − sinh² = 1`. -/
theorem isSpinElem_transportElem (l : ℝ) : IsSpinElem (transportElem l) := by
  have hkey : Real.cosh (l / 2) * Real.cosh (l / 2)
      + Real.sinh (l / 2) * (-Real.sinh (l / 2)) = 1 := by
    have h := Real.cosh_sq_sub_sinh_sq (l / 2)
    rw [pow_two, pow_two] at h
    rw [mul_neg, ← sub_eq_add_neg]
    exact h
  have hcross : Real.cosh (l / 2) * (-Real.sinh (l / 2))
      + Real.sinh (l / 2) * Real.cosh (l / 2) = 0 := by ring
  have hcross' : Real.cosh (l / 2) * Real.sinh (l / 2)
      + (-Real.sinh (l / 2)) * Real.cosh (l / 2) = 0 := by ring
  have hkey' : Real.cosh (l / 2) * Real.cosh (l / 2)
      + (-Real.sinh (l / 2)) * Real.sinh (l / 2) = 1 := by
    have h := Real.cosh_sq_sub_sinh_sq (l / 2)
    rw [pow_two, pow_two] at h
    rw [neg_mul, ← sub_eq_add_neg]
    exact h
  constructor
  · rw [cconj_transportElem, transportElem, sub_eq_add_neg, ← neg_smul, paravector_mul,
      hkey, hcross, map_one, zero_smul, add_zero]
  · rw [cconj_transportElem, transportElem, sub_eq_add_neg, ← neg_smul, paravector_mul,
      hkey', hcross', map_one, zero_smul, add_zero]

/-- **NEWLY DEFINED (Task 37), PRINCIPAL — the single shared native Spin-side transport
state.**

A one-parameter family inside the project's own intrinsic Spin group, with `λ = 0` the
distinguished **neutral reference** value.  This is the *only* independent transport-side
deformation source of the Task-37 preparation branch. -/
def transportState (l : ℝ) : ↥SpinGroup := mkSpin (isSpinElem_transportElem l)

theorem transportState_val (l : ℝ) :
    ((transportState l : ↥SpinGroup) : Cl3ˣ).val = transportElem l := rfl

/-- **DERIVED (Task 37), the exact neutral value.**  At `λ = 0` the shared transport state is
*literally* the unit of the intrinsic Spin group — not an approximation and not an analogy. -/
theorem transportState_zero : transportState 0 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show transportElem 0 = 1
  unfold transportElem
  rw [zero_div, Real.cosh_zero, Real.sinh_zero, map_one, zero_smul, add_zero]

/-- **DERIVED (Task 37).**  The deformation source is a one-parameter subgroup: deformations
compose additively in `λ`. -/
theorem transportState_add (a b : ℝ) :
    transportState (a + b) = transportState a * transportState b := by
  refine Subtype.ext (Units.ext ?_)
  show transportElem (a + b) = transportElem a * transportElem b
  unfold transportElem
  rw [paravector_mul, add_div, Real.cosh_add, Real.sinh_add,
    mul_comm (Real.cosh (a / 2)) (Real.sinh (b / 2)),
    add_comm (Real.sinh (a / 2) * Real.cosh (b / 2))
      (Real.sinh (b / 2) * Real.cosh (a / 2))]

/-- **DERIVED (Task 37).**  The inverse deformation is the opposite parameter. -/
theorem transportState_neg (a : ℝ) : transportState (-a) = (transportState a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← transportState_add, neg_add_cancel, transportState_zero]

/-! ## The derived Lorentz-side datum -/

/-- **DERIVED (Task 37).**  The projected Lorentz-side transport state.  It is *defined* as the
image of the Spin-side state under the project's own covering homomorphism; there is no
independent Lorentz-side parameter anywhere in this branch. -/
def projectedTransportState (l : ℝ) : ↥GLor := spinCover (transportState l)

/-- **DERIVED (Task 37).**  Exact neutral regression on the Lorentz side. -/
theorem projectedTransportState_zero : projectedTransportState 0 = 1 := by
  rw [projectedTransportState, transportState_zero, map_one]

/-- **DERIVED (Task 37), the shared-origin law.**  Two deformation parameters with the same
Spin-side state have the same projected Lorentz-side state.  This is the theorem-level form of
the §18 firewall: the Lorentz datum is a *function* of the Spin datum. -/
theorem projected_determined_by_spin {a b : ℝ} (h : transportState a = transportState b) :
    projectedTransportState a = projectedTransportState b := by
  rw [projectedTransportState, projectedTransportState, h]

/-- **DERIVED (Task 37).**  The action of the projected transport state on the intrinsic unit
`1_𝒮` of the carrier is the explicit paravector `(cosh λ, sinh λ · e₀)`. -/
theorem projectedTransportState_apply_sOne (l : ℝ) :
    ((projectedTransportState l : ↥GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne
      = (Real.cosh l, Real.sinh l • evec 0) := by
  show spinLor (transportElem l) sOne = _
  refine spinLor_unique ?_
  have hrev : CliffordAlgebra.reverse (Q := q3) (transportElem l) = transportElem l := by
    unfold transportElem cle
    rw [map_add, map_smul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse.commutes]
  have hone : spinToCl sOne = 1 := by
    unfold spinToCl sOne
    rw [map_zero, add_zero, map_one]
  have hc : Real.cosh l
      = Real.cosh (l / 2) * Real.cosh (l / 2) + Real.sinh (l / 2) * Real.sinh (l / 2) := by
    conv_lhs => rw [show l = 2 * (l / 2) by ring]
    rw [Real.cosh_two_mul, pow_two, pow_two]
  have hs : Real.sinh l
      = Real.cosh (l / 2) * Real.sinh (l / 2) + Real.sinh (l / 2) * Real.cosh (l / 2) := by
    conv_lhs => rw [show l = 2 * (l / 2) by ring]
    rw [Real.sinh_two_mul]
    ring
  have hsq : transportElem l * transportElem l
      = algebraMap ℝ Cl3 (Real.cosh l) + Real.sinh l • cle 0 := by
    unfold transportElem
    rw [paravector_mul, hc, hs]
  have hpara : spinToCl ((Real.cosh l, Real.sinh l • evec 0) : LorentzCarrier)
      = algebraMap ℝ Cl3 (Real.cosh l) + Real.sinh l • cle 0 := by
    unfold spinToCl cle
    rw [map_smul]
  rw [hpara, spinAct, hone, mul_one, hrev, hsq]

/-- **DERIVED (Task 37), PRINCIPAL — the deformation is *visible* after projection.**

For every nonzero `λ` the projected Lorentz-side transport state is **not** the identity.  This
is the exact sense in which the Task-37 deformation source differs from the Task-36 kernel
(`±1`) twist, which is invisible after projection: a nonzero deformation really does change
the Lorentz-side datum that the solder has to intertwine.  Whether the *global closure* still
admits a solution is a different question, and it is the open question of Task 38. -/
theorem projectedTransportState_ne_one {l : ℝ} (hl : l ≠ 0) :
    projectedTransportState l ≠ 1 := by
  intro h
  have hact := projectedTransportState_apply_sOne l
  rw [h] at hact
  have h2 : ((1 : ↥GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne := rfl
  rw [h2] at hact
  have hsnd : (0 : Fin 3 → ℝ) = Real.sinh l • evec 0 := congrArg Prod.snd hact
  have hz := congrFun hsnd 0
  rw [Pi.smul_apply, evec, smul_eq_mul, if_pos rfl, mul_one] at hz
  exact hl (Real.sinh_eq_zero.1 hz.symm)

/-- **DERIVED (Task 37).**  Distinct finite deformation parameters give distinct shared
transport states, so the parameter is not degenerate. -/
theorem transportState_injective {a b : ℝ} (h : transportState a = transportState b) : a = b := by
  have h1 : transportState (a - b) = 1 := by
    rw [sub_eq_add_neg, transportState_add, transportState_neg, h, mul_inv_cancel]
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero_of_ne hne
  exact projectedTransportState_ne_one hab (by rw [projectedTransportState, h1, map_one])

/-! ## The deformation-family interface

The families below are deliberately *parameter-type generic*: the first smoke test uses the
constant scalar parameter `P = ℝ`, while a later inhomogeneous experiment may use a local
parameter field (for instance `P = LocalModel → ℝ`, a "`λ(x)`" sector).  Nothing in the
interface forces the parameter to be a single real number, so the mixed/inhomogeneous
extension needs no redesign. -/

universe t u

/-- **NEWLY DEFINED (Task 37), PRINCIPAL — the co-varying (MAIN TEST B) family.**

A deformation family assigns to every parameter value a base gluing datum *and* a native Spin
transition datum over the emergent cover of that base.  The Lorentz side is **not** a field:
it is obtained from the Spin field by the native projection.

The base is allowed to co-vary with the parameter, because the project hypothesis is about
reciprocal closure: the relational geometry and the transport are not independent. -/
structure SharedTransportFamily (P : Type u) (ι : Type t) where
  /-- The (possibly parameter-dependent) base gluing datum. -/
  base : P → BaseGluingData LocalModel ι
  /-- The native Spin transition datum over the emergent cover of that base. -/
  spin : ∀ p : P, NativeSpinTransitionData ↥SpinGroup (emergentCover (base p))

/-- The scalar smoke-test case: one real deformation parameter with neutral value `0`. -/
abbrev ScalarTransportFamily (ι : Type t) := SharedTransportFamily ℝ ι

namespace SharedTransportFamily

variable {P : Type u} {ι : Type t}

/-- **DERIVED (Task 37).**  The projected Lorentz transition system of a family at a parameter
value.  It is a *derived* object: nothing in `SharedTransportFamily` can tune it separately. -/
def projectedLorentz (F : SharedTransportFamily P ι) (p : P) (i j : ι)
    (x : Space (F.base p)) : LocalModel ≃ₗ[ℝ] LocalModel :=
  projectedLorentzTransition (F.spin p) i j x

/-- **DERIVED (Task 37), §18 shared-origin firewall, definitional form.**  The projected
Lorentz transition of a family is *by definition* the projection of its Spin field; there is
no second field to adjust. -/
theorem projectedLorentz_eq (F : SharedTransportFamily P ι) (p : P) (i j : ι)
    (x : Space (F.base p)) :
    F.projectedLorentz p i j x = projectedLorentzTransition (F.spin p) i j x := rfl

/-- The **fixed-base (CONTROL A)** family built from one frozen base and a parameter-dependent
Spin datum over it: the Spin-side transport varies, the relational geometry does not. -/
def fixedBase {B : BaseGluingData LocalModel ι}
    (S : P → NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    SharedTransportFamily P ι where
  base := fun _ => B
  spin := S

theorem fixedBase_base {B : BaseGluingData LocalModel ι}
    (S : P → NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (p : P) :
    (fixedBase S).base p = B := rfl

theorem fixedBase_spin {B : BaseGluingData LocalModel ι}
    (S : P → NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (p : P) :
    (fixedBase S).spin p = S p := rfl

/-- **DERIVED (Task 37), §18 shared-origin firewall, fixed-base form.**  Over one frozen base,
two deformation families with the same Spin field at a parameter value have *the same*
projected Lorentz transition system: the Lorentz side carries no independent knob. -/
theorem fixedBase_projectedLorentz_determined {B : BaseGluingData LocalModel ι}
    (S S' : P → NativeSpinTransitionData ↥SpinGroup (emergentCover B)) {p : P}
    (h : S p = S' p) :
    (fixedBase S).projectedLorentz p = (fixedBase S').projectedLorentz p := by
  show projectedLorentzTransition (S p) = projectedLorentzTransition (S' p)
  rw [h]

end SharedTransportFamily

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.transportState
#print axioms Task37.Deformation.transportState_zero
#print axioms Task37.Deformation.transportState_add
#print axioms Task37.Deformation.transportState_neg
#print axioms Task37.Deformation.projectedTransportState_zero
#print axioms Task37.Deformation.projected_determined_by_spin
#print axioms Task37.Deformation.projectedTransportState_apply_sOne
#print axioms Task37.Deformation.projectedTransportState_ne_one
#print axioms Task37.Deformation.transportState_injective
#print axioms Task37.Deformation.SharedTransportFamily
#print axioms Task37.Deformation.SharedTransportFamily.projectedLorentz_eq
#print axioms Task37.Deformation.SharedTransportFamily.fixedBase_projectedLorentz_determined
