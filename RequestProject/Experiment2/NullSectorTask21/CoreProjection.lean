import RequestProject.Experiment2.NullSectorTask21.VisibleRotationCandidate

/-!
# Task 21, Package E: identification of the intrinsic core projection

**IDENTIFICATION / COMPARISON MODULE.**

The intrinsic projection `proj` is frozen.  Under the Package-A equivalence it is computed
on `fromQuat q` and compared *pointwise* with the standard quaternion-conjugation action on
the imaginary three-space.  The kernel theorem is then recovered through the identified
lower map — it is **not** used to infer that the two maps agree (item 54).

`IMPORTED STANDARD RESULT`: the quaternion algebra and its star operation.

`DERIVED IN TASK 21`: every statement below.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

open Quaternion Matrix

/-! ## The standard quaternionic rotation action -/

/-- **COMPARISON.**  The imaginary quaternion attached to a spatial vector. -/
def imQ (p : Vec3) : ℍ := ⟨0, p.1, p.2.1, p.2.2⟩

/-- **COMPARISON.**  The spatial vector of the imaginary part of a quaternion. -/
def imPart (q : ℍ) : Vec3 := (q.imI, q.imJ, q.imK)

/-- **COMPARISON.**  The standard quaternionic rotation action on the imaginary
three-space. -/
def quatConj (q : ℍ) (p : Vec3) : Vec3 := imPart (q * imQ p * star q)

/-- **COMPARISON.**  The matrix of the standard quaternionic rotation action. -/
def quatRotMat (q : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => vc (quatConj q (be j)) i

/-! ## The intrinsic inverse of a unit-quaternion image -/

theorem quat_mul_star_of_normSq_one {q : ℍ} (hq : Quaternion.normSq q = 1) :
    q * star q = 1 := by
  rw [Quaternion.mul_star_eq_coe]
  have hre : (q * star q).re = Quaternion.normSq q := by
    simp [Quaternion.normSq_def']
    ring
  rw [hre, hq]
  simp

theorem quat_star_mul_of_normSq_one {q : ℍ} (hq : Quaternion.normSq q = 1) :
    star q * q = 1 := by
  rw [Quaternion.star_mul_self, hq]
  simp

theorem invW_fromQuat {q : ℍ} (hq : Quaternion.normSq q = 1) :
    invW (fromQuat q) = fromQuat (star q) := by
  refine invW_eq ?_ ?_
  · rw [← fromQuat_mul, quat_mul_star_of_normSq_one hq, fromQuat_one]
  · rw [← fromQuat_mul, quat_star_mul_of_normSq_one hq, fromQuat_one]

/-! ## Package E, principal computation -/

/-- **PACKAGE E (items 48–50).**  The intrinsic projection of the image of a unit quaternion
acts on the inherited spatial sector exactly as the standard quaternion conjugation acts on
the imaginary three-space.  The two actions are compared pointwise. -/
theorem spatAct_proj_fromQuat {q : ℍ} (hq : Quaternion.normSq q = 1) (p : Vec3) :
    spatAct (proj (fromQuat q)) p = quatConj q p := by
  rw [spatAct_apply, proj_apply, invW_fromQuat hq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [spatInv, fromQuat, Jmap, spat, sp, iota3, w1, wP, wQ, wR, wit8MulFun,
      quatConj, imQ, imPart] <;> ring

/-- **PACKAGE E.**  The same statement at matrix level. -/
theorem rotMat_proj_fromQuat {q : ℍ} (hq : Quaternion.normSq q = 1) :
    rotMat (proj (fromQuat q)) = quatRotMat q := by
  refine Matrix.ext fun i j => ?_
  rw [rotMat, Matrix.of_apply, quatRotMat, Matrix.of_apply, spatAct_proj_fromQuat hq]

/-- **PACKAGE E (item 51).**  The complete comparison diagram commutes pointwise: going down
the Package-A equivalence, along the intrinsic projection and across the Package-C/D
identification gives exactly the standard quaternionic rotation matrix. -/
theorem coreProjection_diagram (q : UQ) :
    ((toRot (projCore (liftQuatEquiv q)) : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) = quatRotMat (q : ℍ) := by
  show rotMat (proj (fromQuat (q : ℍ))) = quatRotMat (q : ℍ)
  exact rotMat_proj_fromQuat (UQ_normSq q)

/-- **PACKAGE E (item 53).**  The kernel theorem, recovered through the identified lower
map: the unit quaternions whose standard rotation matrix is the identity are exactly `±1`.
This is proved from the identified action, not inherited from the intrinsic kernel. -/
theorem quatRot_kernel (q : UQ) :
    quatRotMat (q : ℍ) = 1 ↔ ((q : ℍ) = 1 ∨ (q : ℍ) = -1) := by
  have hq : Quaternion.normSq (q : ℍ) = 1 := UQ_normSq q
  have hmem : fromQuat (q : ℍ) ∈ Lift := fromQuat_mem_Lift hq
  constructor
  · intro h
    have hrot : rotMat (proj (fromQuat (q : ℍ))) = 1 := by
      rw [rotMat_proj_fromQuat hq, h]
    have hid : proj (fromQuat (q : ℍ)) = LinearMap.id :=
      proj_eq_id_of_spatAct_id hmem (spatAct_eq_id_of_rotMat_one hrot)
    have hker : fromQuat (q : ℍ) ∈ ({w1, -w1} : Set W) := by
      rw [← kernel_core]; exact ⟨hmem, hid⟩
    rcases hker with h1 | h1
    · left
      have := congrArg quatOf h1
      rwa [quatOf_fromQuat, show quatOf w1 = 1 by
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp [quatOf, w1]] at this
    · right
      have := congrArg quatOf h1
      rwa [quatOf_fromQuat, show quatOf (-w1 : W) = -1 by
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp [quatOf, w1]] at this
  · intro h
    refine Matrix.ext fun i j => ?_
    rcases h with h1 | h1 <;>
      · rw [quatRotMat, Matrix.of_apply, h1]
        fin_cases i <;> fin_cases j <;>
          simp [quatConj, imQ, imPart, be, vc, Matrix.one_apply, Quaternion.ext_iff]

/-- **PACKAGE E (item 55).**  Surjectivity of the intrinsic projection onto the visible
image, inherited from the Task-20 implementation theorem and repackaged. -/
theorem projCore_surjective' : Function.Surjective projCore := projCore_surjective

end NullSectorTask21
