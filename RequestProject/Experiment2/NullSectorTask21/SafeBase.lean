import RequestProject.Experiment2.NullSectorTask20.NegativeControls

/-!
# Task 21, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The single import is `RequestProject.Experiment2.NullSectorTask20.NegativeControls`, the last
*reconstruction* module of Task 20.  Through it, and only through it, Task 21 inherits the
complete Task-20 reconstruction development and, transitively, the reconstruction layers of
Tasks 1–19:

* the associative carrier `W` with product `⋆`, unit `w1`, the central element `wS`, the
  central plane `zc`, the central one-parameter elements `zexp`;
* the spatial carrier `Vec3`, the inherited form `h3`, the spatial embedding `spat`, the
  axis-to-generator map `Jmap`, the reference implementers `Un`, the visible family
  `PhiGen` and the derived spatial coordinate action `rotv`;
* the Task-20 internal carriers `Lift`, `CUnit`, `LiftZ`, the intrinsic projection `proj`,
  the visible parameter carrier `VisParam`, the visible map `visMap`, the visible relation
  `visRel`, the visible quotient `VisQuot`, the visible image `visImage`;
* the Task-20 kernel, centre, relative-factor, torsor and section theorems.

**Firewall.**  This module and `RequestProject.Experiment2.NullSectorTask21.GroupPackaging` are the two
*reconstruction* modules of Task 21: no conventional named group, matrix algebra, quaternion
algebra or complex number occurs in either of them.  Everything that follows in the source
order is an explicitly labelled **identification / comparison** module.

## Content of this module

Purely intrinsic bookkeeping inside the inherited carrier:

* the coordinate expansion of a carrier element in the eight inherited basis elements;
* the products of the three inherited spatial basis elements, which show that the inherited
  carrier is generated as an algebra by its spatial sector;
* the resulting rigidity lemma: a linear, unital, multiplicative self-map of the carrier
  which fixes the spatial sector pointwise is the identity;
* the coordinate retraction `spatInv` of the spatial embedding.
-/

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-! ## Coordinate expansion -/

/-- **DERIVED.**  Every element of the inherited carrier is the coordinate combination of the
eight inherited basis elements. -/
theorem W_expand (x : W) :
    x = x 0 • w1 + x 1 • wA + x 2 • wB + x 3 • wC
        + x 4 • wP + x 5 • wQ + x 6 • wR + x 7 • wS := by
  funext i
  fin_cases i <;> simp [w1, wA, wB, wC, wP, wQ, wR, wS]

/-! ## The spatial sector generates the carrier -/

theorem wA_mul_wB : wA ⋆ wB = wP := by
  funext i; fin_cases i <;> simp [wA, wB, wP]

theorem wB_mul_wC : wB ⋆ wC = wR := by
  funext i; fin_cases i <;> simp [wB, wC, wR]

theorem wC_mul_wA : wC ⋆ wA = -wQ := by
  funext i; fin_cases i <;> simp [wC, wA, wQ]

theorem wR_mul_wA : wR ⋆ wA = wS := by
  funext i; fin_cases i <;> simp [wR, wA, wS]

theorem spat_e1 : spat ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = wA := spat_wA
theorem spat_e2 : spat ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = wB := spat_wB
theorem spat_e3 : spat ((0 : ℝ), (0 : ℝ), (1 : ℝ)) = wC := spat_wC

/-- **DERIVED (rigidity).**  A real-linear self-map of the inherited carrier which is unital,
multiplicative and fixes the inherited spatial sector pointwise is the identity map.  This is
the exact sense in which the spatial sector determines a visible transformation. -/
theorem linear_eq_id_of_fixes_spat (F : W →ₗ[ℝ] W) (hone : F w1 = w1)
    (hmul : ∀ x y : W, F (x ⋆ y) = F x ⋆ F y)
    (hspat : ∀ p : Vec3, F (spat p) = spat p) : F = LinearMap.id := by
  have hA : F wA = wA := by rw [← spat_e1, hspat]
  have hB : F wB = wB := by rw [← spat_e2, hspat]
  have hC : F wC = wC := by rw [← spat_e3, hspat]
  have hP : F wP = wP := by rw [← wA_mul_wB, hmul, hA, hB]
  have hR : F wR = wR := by rw [← wB_mul_wC, hmul, hB, hC]
  have hQ : F wQ = wQ := by
    have h : F (-wQ) = -wQ := by rw [← wC_mul_wA, hmul, hC, hA]
    have h' := congrArg (fun y : W => -y) h
    simpa using h'
  have hS : F wS = wS := by rw [← wR_mul_wA, hmul, hR, hA]
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [W_expand x]
  simp only [map_add, map_smul, hone, hA, hB, hC, hP, hQ, hR, hS, LinearMap.id_apply]
  exact (W_expand x).symm

/-! ## The coordinate retraction of the spatial embedding -/

/-- **NEUTRAL DEFINITION.**  The coordinate retraction of the inherited spatial embedding. -/
def spatInv (x : W) : Vec3 := (x 1, x 2, x 3)

@[simp] theorem spatInv_spat (p : Vec3) : spatInv (spat p) = p := rfl

theorem spatInv_add (x y : W) : spatInv (x + y) = spatInv x + spatInv y := rfl

theorem spatInv_smul (c : ℝ) (x : W) : spatInv (c • x) = c • spatInv x := rfl

theorem spat_injective : Function.Injective spat := by
  intro p q h
  have h' := congrArg spatInv h
  simpa using h'

end NullSectorTask21
