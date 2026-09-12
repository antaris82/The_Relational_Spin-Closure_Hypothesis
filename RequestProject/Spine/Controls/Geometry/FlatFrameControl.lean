import RequestProject.Spine.Geometry.TangentInstance

/-!
# Native control for Task 4 : non-vacuity and non-uniqueness

Two controls, both downstream of the production layer.

## 1. Non-vacuity

`LorentzFrames.Control.flatFrameData` exhibits genuine oriented, time-oriented,
Lorentz-orthonormal frame data over an arbitrary topological base: the fibre is the
intrinsic carrier itself, the metric is the intrinsic polarized form `B_𝒮`, the orientation
is the intrinsic coordinate volume, the time orientation is the intrinsic unit, and every
frame is the identity.  Its transition data is the constant unit, and it carries a Spin
structure, so none of the Task-4 theorems is about an empty class of objects.

**Interpretation boundary.**  This witness is a *model datum*, not a claim about spacetime.
It says nothing about flatness of any connection, absence of curvature or torsion, or any
dynamical statement; it merely shows the definitions are inhabited.

## 2. Non-uniqueness (the `w₂ = 0 ⇏ unique Spin structure` control)

`LorentzFrames.Control.two_distinct_spinFrameStructures` exhibits, on a two-patch cover of a
nonempty base, **two different Spin structures on the same Lorentz frame data**, differing
by the nontrivial `{±1}`-valued Čech 1-cocycle.  Vanishing of the Lorentz-frame Spin-lift
obstruction therefore does not select a Spin structure.
-/

noncomputable section

namespace LorentzFrames

namespace Control

open SpinCore CechSpinLift NullSectorTask28

universe u t

variable (X : Type u) [TopologicalSpace X] (ι : Type t) [Nonempty ι]

/-- The intrinsic polarized form as a bilinear map: the metric of the control datum. -/
def BSbilin : LorentzCarrier →ₗ[ℝ] LorentzCarrier →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ BS BS_add_left BS_smul_left BS_add_right BS_smul_right

@[simp] theorem BSbilin_apply (u v : LorentzCarrier) : BSbilin u v = BS u v := rfl

/-- The one-patch-per-index cover by the whole base. -/
def trivialCover : CechCover X ι where
  U _ := Set.univ
  isOpen_U _ := isOpen_univ
  covers x := ⟨Classical.arbitrary ι, Set.mem_univ x⟩

/-- **CONTROL (non-vacuity).**  Genuine oriented, time-oriented, Lorentz-orthonormal frame
data over an arbitrary topological base, with the intrinsic carrier as fibre. -/
def flatFrameData : LorentzFrameData X (fun _ : X => LorentzCarrier) ι where
  cover := trivialCover X ι
  metric _ := BSbilin
  vol _ := carrierBasis.det
  timeField _ := sOne
  timelike_timeField _ := by
    show 0 < BS sOne sOne
    rw [BS_self, NS_sOne]; norm_num
  frame _ _ := LinearEquiv.refl ℝ LorentzCarrier
  orthonormal _ _ _ _ _ := rfl
  futureDirected _ _ _ := by
    show 0 < BS sOne sOne
    rw [BS_self, NS_sOne]; norm_num
  positivelyOriented _ _ _ := by
    show 0 < carrierBasis.det (fun k => carrierBasis k)
    rw [Module.Basis.det_self]
    norm_num
  continuousOn_comparison _ _ := by
    apply continuousOn_const.congr
    intro x _
    rfl

@[simp] theorem flatFrameData_comparison (i j : ι) (x : X) :
    (flatFrameData X ι).comparison i j x = LinearEquiv.refl ℝ LorentzCarrier := rfl

/-- The transition data of the control datum is the constant unit. -/
@[simp] theorem flatFrameData_transition (i j : ι) (x : X) :
    (flatFrameData X ι).transition i j x = 1 := by
  have hx : x ∈ (flatFrameData X ι).cover.overlap₂ i j := ⟨Set.mem_univ x, Set.mem_univ x⟩
  apply Subtype.ext
  rw [LorentzFrameData.transition_val_of_mem _ hx, flatFrameData_comparison]
  rfl

/-- **CONTROL (non-vacuity).**  The control datum carries a Spin structure: the constant
unit Spin-valued cocycle. -/
def flatSpinStructure : SpinFrameStructure (flatFrameData X ι) where
  s _ _ _ := 1
  continuousOn_s _ _ := continuousOn_const
  projects i j x _ := by rw [map_one, flatFrameData_transition]
  cocycle _ _ _ _ _ := one_mul 1

/-- **CONTROL (non-vacuity).**  The Lorentz-frame Spin-lift obstruction of the control datum
vanishes, and its vanishing is *not* vacuous: a Spin structure really exists. -/
theorem flat_obstruction_vanishes (D : FrameSpinLifts (flatFrameData X ι)) :
    LorentzFrameData.frameObstruction D
      = trivialClass internalSpinProjection (flatFrameData X ι).cover :=
  (LorentzFrameData.frameObstruction_eq_trivial_iff_spinStructure D).2
    ⟨flatSpinStructure X ι⟩

/-! ## Non-uniqueness -/

variable {X}

/-- The nontrivial `{±1}`-valued Čech 1-cocycle of a two-patch cover: `-1` off the
diagonal. -/
def signCocycle : KerCocycle₁ (flatFrameData X Bool) where
  e i j _ := if i = j then 1 else negOneSpin
  isKer i j := by
    refine ⟨continuousOn_const, fun x _ => ?_⟩
    by_cases h : i = j
    · simp only [h, if_pos]
      exact Subgroup.one_mem _
    · simp only [if_neg h]
      exact (mem_ker_spinCover_iff _).2 (Or.inr rfl)
  cocycle i j k x _ := by
    have hsq : negOneSpin * negOneSpin = 1 := by
      have h := negOneSpin_sq
      rwa [pow_two] at h
    cases i <;> cases j <;> cases k <;> simp [hsq]

/-- **CONTROL (WP8 / negative control), principal.**  On a two-patch cover of a nonempty
base, the same Lorentz frame data carries **two different Spin structures**: vanishing of
the Lorentz-frame Spin-lift obstruction does not determine a Spin structure.

This is the formal negative control for `w₂ = 0 ⇏ unique Spin structure`. -/
theorem two_distinct_spinFrameStructures [Nonempty X] :
    ∃ S S' : SpinFrameStructure (flatFrameData X Bool),
      ∃ i j : Bool, ∃ x : X, S.s i j x ≠ S'.s i j x := by
  classical
  refine ⟨flatSpinStructure X Bool, (flatSpinStructure X Bool).twist signCocycle,
    false, true, Classical.arbitrary X, ?_⟩
  show (1 : ↥SpinGroup) ≠ (if (false : Bool) = true then 1 else negOneSpin) * 1
  simp only [if_neg (by decide : ¬((false : Bool) = true)), mul_one]
  exact fun h => negOneSpin_ne_one h.symm

end Control

end LorentzFrames
