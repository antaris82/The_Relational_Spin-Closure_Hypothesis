import RequestProject.Experiment2.NullSectorTask21.GroupPackaging
import RequestProject.Experiment2.NullSectorTask20.Identification

/-!
# Task 21, Package A: the core carrier as a group of unit quaternions

**IDENTIFICATION / COMPARISON MODULE.**  This is the first module of the identification
layer.  It imports the single Task-20 comparison module in order to *reuse* — not to
re-create — the Task-20 map `fromQuat` and the Task-20 image theorem
`lift_eq_image_unit_quaternions`.

What is added here, and is new:

* an explicit inverse map `quatOf : W → ℍ`, read off from the coefficient uniqueness of the
  intrinsic normal form;
* both inverse identities;
* the packaging of the Task-20 image theorem as a **group equivalence**
  `liftQuatEquiv : UQ ≃* LiftG` between the unit quaternions and the intrinsic core carrier,
  with identity, multiplication and inversion preserved;
* the topological strengthening: the same maps are a homeomorphism between the unit sphere
  of `ℍ` and the intrinsic core carrier with its subspace topology.

`IMPORTED STANDARD RESULT`: the quaternion algebra `ℍ = Quaternion ℝ`, its norm, and the
group structure of its unit sphere (`Mathlib/Analysis/Quaternion.lean`,
`Mathlib/Analysis/Normed/Field/UnitBall.lean`).

`DERIVED IN TASK 21`: everything else in this module.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

open Quaternion

/-! ## The unit quaternion group -/

/-- **COMPARISON.**  The standard carrier of unit quaternions, with its standard group
structure. -/
abbrev UQ : Type := Metric.sphere (0 : ℍ) 1

theorem norm_eq_one_iff_normSq (q : ℍ) : ‖q‖ = 1 ↔ normSq q = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self]
  constructor
  · intro h; rw [h]; ring
  · intro h; nlinarith [norm_nonneg q]

theorem mem_UQ_iff (q : ℍ) : q ∈ Metric.sphere (0 : ℍ) 1 ↔ normSq q = 1 := by
  rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_normSq]

theorem UQ_normSq (q : UQ) : normSq (q : ℍ) = 1 := (mem_UQ_iff _).1 q.2

theorem UQ_ne_zero (q : UQ) : (q : ℍ) ≠ 0 := by
  intro h
  have := UQ_normSq q
  rw [h, map_zero] at this
  exact zero_ne_one this

/-! ## The forward map, reusing the Task-20 map -/

theorem fromQuat_mem_Lift {q : ℍ} (hq : normSq q = 1) : fromQuat q ∈ Lift := by
  rw [lift_eq_image_unit_quaternions]
  exact ⟨q, hq, rfl⟩

/-- **DERIVED.**  The packaged invertible carrier element attached to a unit quaternion. -/
noncomputable def quatWG (q : UQ) : WG where
  val := fromQuat (q : ℍ)
  inv := fromQuat ((q : ℍ)⁻¹)
  val_inv := by
    rw [← fromQuat_mul, mul_inv_cancel₀ (UQ_ne_zero q), fromQuat_one]
  inv_val := by
    rw [← fromQuat_mul, inv_mul_cancel₀ (UQ_ne_zero q), fromQuat_one]

@[simp] theorem quatWG_val (q : UQ) : (quatWG q).val = fromQuat (q : ℍ) := rfl

theorem quatWG_mem_LiftG (q : UQ) : quatWG q ∈ LiftG := fromQuat_mem_Lift (UQ_normSq q)

/-- **PACKAGE A.**  The forward group homomorphism from unit quaternions to the intrinsic
core carrier. -/
noncomputable def toLiftG : UQ →* LiftG where
  toFun q := ⟨quatWG q, quatWG_mem_LiftG q⟩
  map_one' := by
    refine Subtype.ext (WG.ext ?_)
    show fromQuat ((1 : UQ) : ℍ) = w1
    rw [Metric.unitSphere.coe_one, fromQuat_one]
  map_mul' q p := by
    refine Subtype.ext (WG.ext ?_)
    show fromQuat ((q * p : UQ) : ℍ) = fromQuat (q : ℍ) ⋆ fromQuat (p : ℍ)
    rw [Metric.unitSphere.coe_mul, fromQuat_mul]

@[simp] theorem toLiftG_val (q : UQ) : ((toLiftG q : LiftG) : WG).val = fromQuat (q : ℍ) := rfl

/-! ## The inverse map, from coefficient uniqueness -/

/-- **PACKAGE A.**  The explicit inverse map: the quaternion coefficients are read off from
the carrier coordinates of the intrinsic normal form. -/
def quatOf (x : W) : ℍ := ⟨x 0, -(x 6), x 5, -(x 4)⟩

@[simp] theorem quatOf_re (x : W) : (quatOf x).re = x 0 := rfl
@[simp] theorem quatOf_imI (x : W) : (quatOf x).imI = -(x 6) := rfl
@[simp] theorem quatOf_imJ (x : W) : (quatOf x).imJ = x 5 := rfl
@[simp] theorem quatOf_imK (x : W) : (quatOf x).imK = -(x 4) := rfl

theorem fromQuat_coord (q : ℍ) :
    fromQuat q 0 = q.re ∧ fromQuat q 4 = -q.imK ∧ fromQuat q 5 = q.imJ ∧
      fromQuat q 6 = -q.imI := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [fromQuat, w1, Jmap, wP, wQ, wR]

/-- **PACKAGE A (first inverse identity).** -/
@[simp] theorem quatOf_fromQuat (q : ℍ) : quatOf (fromQuat q) = q := by
  obtain ⟨h0, h4, h5, h6⟩ := fromQuat_coord q
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [quatOf_re, quatOf_imI, quatOf_imJ, quatOf_imK, h0, h4, h5, h6, neg_neg]

/-- **PACKAGE A (second inverse identity, on the core carrier).** -/
theorem fromQuat_quatOf {u : W} (hu : u ∈ Lift) : fromQuat (quatOf u) = u := by
  rw [lift_eq_image_unit_quaternions] at hu
  obtain ⟨q, -, rfl⟩ := hu
  rw [quatOf_fromQuat]

theorem quatOf_normSq {u : W} (hu : u ∈ Lift) : normSq (quatOf u) = 1 := by
  rw [lift_eq_image_unit_quaternions] at hu
  obtain ⟨q, hq, rfl⟩ := hu
  rwa [quatOf_fromQuat]

/-- **PACKAGE A.**  The backward map. -/
def ofLiftG (u : LiftG) : UQ :=
  ⟨quatOf ((u : WG).val), (mem_UQ_iff _).2 (quatOf_normSq u.2)⟩

@[simp] theorem ofLiftG_coe (u : LiftG) : ((ofLiftG u : UQ) : ℍ) = quatOf ((u : WG).val) := rfl

/-! ## The group equivalence -/

/-- **PACKAGE A, principal.**  The intrinsic core carrier is *exactly* the group of unit
quaternions: an explicit multiplicative equivalence, with explicit inverse. -/
noncomputable def liftQuatEquiv : UQ ≃* LiftG where
  toFun := toLiftG
  invFun := ofLiftG
  left_inv q := by
    refine Subtype.ext ?_
    rw [ofLiftG_coe, toLiftG_val, quatOf_fromQuat]
  right_inv u := by
    refine Subtype.ext (WG.ext ?_)
    rw [toLiftG_val, ofLiftG_coe, fromQuat_quatOf u.2]
  map_mul' := map_mul toLiftG

@[simp] theorem liftQuatEquiv_apply (q : UQ) : liftQuatEquiv q = toLiftG q := rfl

@[simp] theorem liftQuatEquiv_symm_apply (u : LiftG) : liftQuatEquiv.symm u = ofLiftG u := rfl

/-- **PACKAGE A (item 14): identity is preserved.** -/
theorem liftQuatEquiv_one : liftQuatEquiv 1 = 1 := map_one liftQuatEquiv

/-- **PACKAGE A (item 14): multiplication is preserved.** -/
theorem liftQuatEquiv_mul (q p : UQ) :
    liftQuatEquiv (q * p) = liftQuatEquiv q * liftQuatEquiv p := map_mul liftQuatEquiv q p

/-- **PACKAGE A (item 14): inversion is preserved.** -/
theorem liftQuatEquiv_inv (q : UQ) : liftQuatEquiv q⁻¹ = (liftQuatEquiv q)⁻¹ :=
  map_inv liftQuatEquiv q

/-- **PACKAGE A (item 16): both inverse identities, in packaged form.** -/
theorem liftQuatEquiv_inverse_identities :
    (∀ q : UQ, ofLiftG (toLiftG q) = q) ∧ (∀ u : LiftG, toLiftG (ofLiftG u) = u) :=
  ⟨liftQuatEquiv.left_inv, liftQuatEquiv.right_inv⟩

/-! ## The topological strengthening (item 17) -/

/-- The forward map, as a real-linear map of finite-dimensional real vector spaces. -/
noncomputable def fromQuatL : ℍ →ₗ[ℝ] W where
  toFun := fromQuat
  map_add' q p := by
    refine funext fun i => ?_
    fin_cases i <;> simp [fromQuat, w1, Jmap, wP, wQ, wR] <;> ring
  map_smul' c q := by
    refine funext fun i => ?_
    fin_cases i <;> simp [fromQuat, w1, Jmap, wP, wQ, wR] <;> ring

/-- The backward map, as a real-linear map of finite-dimensional real vector spaces. -/
def quatOfL : W →ₗ[ℝ] ℍ where
  toFun := quatOf
  map_add' x y := by
    refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp [quatOf] <;> ring
  map_smul' c x := by
    refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp [quatOf] <;> ring

theorem continuous_fromQuat : Continuous fromQuat :=
  fromQuatL.continuous_of_finiteDimensional

theorem continuous_quatOf : Continuous quatOf :=
  quatOfL.continuous_of_finiteDimensional

/-- **PACKAGE A (item 17).**  The same two maps are mutually inverse homeomorphisms between
the standard unit sphere of `ℍ` and the intrinsic core carrier with its subspace topology.
The algebraic equivalence above and this homeomorphism have the same underlying maps. -/
noncomputable def liftQuatHomeo : UQ ≃ₜ (Lift : Set W) where
  toFun q := ⟨fromQuat (q : ℍ), fromQuat_mem_Lift (UQ_normSq q)⟩
  invFun u := ⟨quatOf (u : W), (mem_UQ_iff _).2 (quatOf_normSq u.2)⟩
  left_inv q := by
    refine Subtype.ext ?_
    simp only [quatOf_fromQuat]
  right_inv u := by
    refine Subtype.ext ?_
    simp only [fromQuat_quatOf u.2]
  continuous_toFun := (continuous_fromQuat.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_quatOf.comp continuous_subtype_val).subtype_mk _

theorem liftQuatHomeo_coe (q : UQ) : (liftQuatHomeo q : W) = ((liftQuatEquiv q : LiftG) : WG).val :=
  rfl

end NullSectorTask21
