import RequestProject.Spine.E2.Cech.Core

/-!
# Native control : the Task-3 Čech obstruction machinery is not vacuous

This is a **control**, downstream of production; no production module imports it.

Two things are checked on an explicit instance built from the *native* intrinsic Spin
projection `SpinCore.internalSpinProjection`:

1. a family of local Spin lifts exists and its triple-overlap defect is **not** the constant
   `1` — so `SpinLiftFamily.defect` genuinely depends on the choice of local
   representatives, and the theorems about it are not statements about a trivial object;
2. nevertheless the obstruction class of the *same* data vanishes, because a coherent family
   of lifts of the same visible data exists.

Together they separate the two layers of Task 3 exactly as the audit requires:

`c_ijk` is CHOICE_UP_TO_KERNEL,  `[c]` is choice-invariant.

The base used is the one-point space with the one-patch cover and the unit transition
cocycle: this is the smallest instance in which the phenomenon can be exhibited, and no
geometric reading whatsoever attaches to it.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpineControls

open CechSpinLift NullSectorTask28 SpinCore

/-- The one-patch cover of the one-point space. -/
def pointCover : CechCover PUnit.{1} PUnit.{1} where
  U _ := Set.univ
  isOpen_U _ := isOpen_univ
  covers _ := ⟨PUnit.unit, Set.mem_univ _⟩

/-- The unit visible transition cocycle on `pointCover`. -/
def unitCocycle : VisibleCocycle (↥GLor) pointCover where
  g _ _ _ := 1
  continuousOn_g _ _ := continuousOn_const
  cocycle _ _ _ _ _ := one_mul 1

/-- The coherent family of local Spin lifts: every transition is lifted by `1`. -/
def coherentLift : SpinLiftFamily internalSpinProjection unitCocycle where
  lift _ _ _ := 1
  isRep _ _ := ⟨continuousOn_const, fun _ _ => map_one _⟩

/-- A second family of local Spin lifts of the *same* unit transition data: every transition
is lifted by the nontrivial central element `-1` of the intrinsic spin group. -/
def negLift : SpinLiftFamily internalSpinProjection unitCocycle where
  lift _ _ _ := negOneSpin
  isRep _ _ := ⟨continuousOn_const, fun _ _ =>
    MonoidHom.mem_ker.1 ((mem_ker_spinCover_iff negOneSpin).2 (Or.inr rfl))⟩

theorem coherentLift_isCoherent : coherentLift.IsCoherent := by
  intro i j k x _
  simp [coherentLift]

/-- **CONTROL 1.**  The defect of the second family is the nontrivial kernel element, so the
defect is genuinely choice-dependent and not identically `1`. -/
theorem negLift_defect_ne_one :
    negLift.defect PUnit.unit PUnit.unit PUnit.unit PUnit.unit = negOneSpin ∧
      negLift.defect PUnit.unit PUnit.unit PUnit.unit PUnit.unit ≠ 1 := by
  refine ⟨?_, ?_⟩
  · simp [SpinLiftFamily.defect_apply, negLift]
  · rw [show negLift.defect PUnit.unit PUnit.unit PUnit.unit PUnit.unit = negOneSpin by
      simp [SpinLiftFamily.defect_apply, negLift]]
    exact negOneSpin_ne_one

/-- **CONTROL 2.**  The obstruction class of the same data nevertheless vanishes, and it is
the same for both families. -/
theorem obstruction_trivial_both :
    negLift.obstruction = trivialClass internalSpinProjection pointCover ∧
      coherentLift.obstruction = negLift.obstruction :=
  ⟨(negLift.obstruction_eq_trivialClass_iff_exists_coherent).2
      ⟨coherentLift, coherentLift_isCoherent⟩,
    coherentLift.obstruction_lift_independent negLift⟩

end SpineControls

#print axioms SpineControls.negLift_defect_ne_one
#print axioms SpineControls.obstruction_trivial_both
