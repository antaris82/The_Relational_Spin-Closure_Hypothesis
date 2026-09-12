import RequestProject.Experiment2.NullSectorTask21.CoreQuaternionEquiv

/-!
# Task 21, Package B: comparison of the unit-quaternion core with one standard named model

**IDENTIFICATION / COMPARISON MODULE.**

Item 20 asks which standard formal model is actually available in the installed library.
The answer, checked against the installed revision, is:

* `Matrix.specialUnitaryGroup (Fin 2) ℂ` — available, and used here as the standard named
  model;
* a named `Spin(3)` model — the library provides `spinGroup` for a general Clifford algebra
  (`Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean`), but no equivalence of it with
  unit quaternions and no three-dimensional specialization.  Constructing one would mean
  duplicating a large standard development, which item 23 forbids; the corresponding verdict
  is therefore `NOT FORMALIZED` and the comparison is documentation-only.

`IMPORTED STANDARD RESULT`: `Matrix.specialUnitaryGroup`, `Matrix.unitaryGroup`
(`Mathlib/LinearAlgebra/Matrix/UnitaryGroup.lean`).

`DERIVED IN TASK 21`: the explicit map `quatMat`, its multiplicativity, injectivity,
surjectivity, and the resulting group equivalence.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask08 NullSectorTask09 NullSectorTask14 NullSectorTask20
open Quaternion Matrix

/-! ## The explicit 2×2 complex matrix of a quaternion -/

/-- **COMPARISON.**  The standard 2×2 complex matrix model of a quaternion. -/
def quatMat (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + (q.imI : ℂ) * Complex.I, (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I;
     -(q.imJ : ℂ) + (q.imK : ℂ) * Complex.I, (q.re : ℂ) - (q.imI : ℂ) * Complex.I]

@[simp] theorem quatMat_00 (q : ℍ) :
    quatMat q 0 0 = (q.re : ℂ) + (q.imI : ℂ) * Complex.I := rfl
@[simp] theorem quatMat_01 (q : ℍ) :
    quatMat q 0 1 = (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I := rfl
@[simp] theorem quatMat_10 (q : ℍ) :
    quatMat q 1 0 = -(q.imJ : ℂ) + (q.imK : ℂ) * Complex.I := rfl
@[simp] theorem quatMat_11 (q : ℍ) :
    quatMat q 1 1 = (q.re : ℂ) - (q.imI : ℂ) * Complex.I := rfl

theorem quatMat_one : quatMat 1 = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.one_apply] <;> norm_num

theorem quatMat_mul (q p : ℍ) : quatMat (q * p) = quatMat q * quatMat p := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_two, Quaternion.mul_re,
      Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK, Complex.ext_iff,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;>
    constructor <;> ring

theorem quatMat_det (q : ℍ) : (quatMat q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  rw [Quaternion.normSq_def']
  simp only [quatMat_00, quatMat_01, quatMat_10, quatMat_11]
  refine Complex.ext ?_ ?_ <;>
    simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow] <;> ring

theorem quatMat_mem_unitary {q : ℍ} (hq : Quaternion.normSq q = 1) :
    quatMat q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hq' : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    rw [← Quaternion.normSq_def']; exact hq
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.star_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;>
    constructor <;> nlinarith [hq']

theorem quatMat_mem_SU {q : ℍ} (hq : Quaternion.normSq q = 1) :
    quatMat q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨quatMat_mem_unitary hq, ?_⟩
  show (quatMat q).det = 1
  rw [quatMat_det, hq]
  norm_num

theorem quatMat_injective : Function.Injective quatMat := by
  intro q p h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [quatMat_00, quatMat_01, Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at h00 h01
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> linarith [h00.1, h00.2, h01.1, h01.2]

/-- **PACKAGE B.**  The forward homomorphism from unit quaternions to the standard special
unitary model. -/
noncomputable def toSU : UQ →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun q := ⟨quatMat (q : ℍ), quatMat_mem_SU (UQ_normSq q)⟩
  map_one' := by
    refine Subtype.ext ?_
    show quatMat ((1 : UQ) : ℍ) = 1
    rw [show ((1 : UQ) : ℍ) = 1 from Metric.unitSphere.coe_one, quatMat_one]
  map_mul' q p := by
    refine Subtype.ext ?_
    show quatMat ((q * p : UQ) : ℍ) = quatMat (q : ℍ) * quatMat (p : ℍ)
    rw [show ((q * p : UQ) : ℍ) = (q : ℍ) * (p : ℍ) from Metric.unitSphere.coe_mul q p,
      quatMat_mul]

theorem toSU_injective : Function.Injective toSU := by
  intro q p h
  have h' : quatMat (q : ℍ) = quatMat (p : ℍ) := congrArg Subtype.val h
  exact Subtype.ext (quatMat_injective h')

theorem toSU_surjective : Function.Surjective toSU := by
  rintro ⟨A, hA, hdet⟩
  have hu : A * star A = 1 := Matrix.mem_unitaryGroup_iff.1 hA
  have hd : A.det = 1 := hdet
  have e00 : A 0 0 * (starRingEnd ℂ) (A 0 0) + A 0 1 * (starRingEnd ℂ) (A 0 1) = 1 := by
    have h := congrFun (congrFun hu 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply] using h
  have e01 : A 0 0 * (starRingEnd ℂ) (A 1 0) + A 0 1 * (starRingEnd ℂ) (A 1 1) = 0 := by
    have h := congrFun (congrFun hu 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply] using h
  have edet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hd
  -- conjugate of the off-diagonal relation
  have e01' : (starRingEnd ℂ) (A 0 0) * A 1 0 + (starRingEnd ℂ) (A 0 1) * A 1 1 = 0 := by
    have := congrArg (starRingEnd ℂ) e01
    simpa using this
  have hw : A 1 1 = (starRingEnd ℂ) (A 0 0) := by
    have h : A 1 1 - (starRingEnd ℂ) (A 0 0) = 0 := by
      linear_combination (-(A 1 1)) * e00 + (starRingEnd ℂ) (A 0 0) * edet + (A 0 1) * e01'
    exact sub_eq_zero.mp h
  have hz : A 1 0 = -(starRingEnd ℂ) (A 0 1) := by
    have h : A 1 0 + (starRingEnd ℂ) (A 0 1) = 0 := by
      linear_combination (-(A 1 0)) * e00 - (starRingEnd ℂ) (A 0 1) * edet + (A 0 0) * e01'
    exact eq_neg_of_add_eq_zero_left h
  refine ⟨⟨⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩, ?_⟩, ?_⟩
  · rw [mem_UQ_iff, Quaternion.normSq_def']
    have hre := congrArg Complex.re e00
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.one_re] at hre
    nlinarith [hre]
  · refine Subtype.ext ?_
    show quatMat _ = A
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> refine Complex.ext ?_ ?_ <;>
      simp [quatMat, hz, hw]

/-- **PACKAGE B, verdict.**  `unit quaternions ≃ SU(2)` — PROVED, by an explicit map with an
explicit inverse. -/
noncomputable def quatSUEquiv : UQ ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective toSU ⟨toSU_injective, toSU_surjective⟩

/-- **PACKAGE B, transported verdict.**  The intrinsic core carrier is group-equivalent to
the standard special unitary model. -/
noncomputable def liftSUEquiv : LiftG ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  liftQuatEquiv.symm.trans quatSUEquiv

end NullSectorTask21
