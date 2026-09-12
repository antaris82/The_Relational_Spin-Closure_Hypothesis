import RequestProject.Experiment2.NullSectorTask23.Task23

/-!
# Task 24, Package A: the metric-oriented three-dimensional carrier, frozen

**PACKAGING LAYER.  Nothing here is rebuilt from coordinates: every structural fact used is
an inherited theorem of the earlier layers, restated under a neutral Task-24 name.**

What is packaged:

* the real three-dimensional carrier `E` (the inherited spatial carrier) with its inherited
  real vector-space structure — *inherited data*;
* the inherited positive-definite form `h3` and its bilinearity/symmetry — *inherited data*,
  with the elementary bilinearity identities proved here directly from the inherited
  definition (they are one-line coordinate computations, not new mathematics);
* the minimal intrinsic orientation datum `triple`, defined from the inherited spatial cross
  product — *newly defined here* (item 17: the inherited orientation datum was available only
  indirectly, through a determinant, so the minimal predicate needed for Task 24 is fixed
  here);
* the visible action `gact` of the inherited visible carrier `GvisG` on `E`, together with
  the two preservation theorems (inner product, orientation) — the inner-product statement is
  an *inherited theorem*, the orientation statement is *derived here* from the inherited
  determinant theorem.

No manifold, tangent bundle, frame bundle, principal bundle, spin structure, characteristic
class or dynamical notion occurs anywhere in the Task-24 layer.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

open Matrix

/-! ## The carriers -/

/-- **INHERITED DATA (item 14).**  The reconstructed real three-dimensional spatial carrier,
with its inherited real vector-space structure.  It is *not* rebuilt here. -/
abbrev E : Type := Vec3

/-- **INHERITED DATA (item 14).**  The reconstructed visible carrier, as the packaged group
of Task 21.  It is *not* redefined here. -/
abbrev Gvis : Type := GvisG

/-- **INHERITED DATA.**  The certified internal carrier, as the packaged group of Task 21. -/
abbrev LiftGrp : Type := LiftG

/-! ## The inherited inner product

`h3` is the inherited positive-definite form on `E`.  The following identities are the
elementary bilinearity/symmetry facts, proved directly from the inherited definition. -/

theorem ip_add_right (x y z : E) : h3 x (y + z) = h3 x y + h3 x z := by
  simp only [h3, dot3, Prod.fst_add, Prod.snd_add]; ring

theorem ip_add_left (x y z : E) : h3 (x + y) z = h3 x z + h3 y z := by
  simp only [h3, dot3, Prod.fst_add, Prod.snd_add]; ring

theorem ip_smul_right (c : ℝ) (x y : E) : h3 x (c • y) = c * h3 x y := by
  simp only [h3, dot3, Prod.smul_def, smul_eq_mul]; ring

theorem ip_smul_left (c : ℝ) (x y : E) : h3 (c • x) y = c * h3 x y := by
  simp only [h3, dot3, Prod.smul_def, smul_eq_mul]; ring

theorem ip_comm (x y : E) : h3 x y = h3 y x := by
  simp only [h3, dot3]; ring

theorem ip_self_eq_zero {x : E} (h : h3 x x = 0) : x = 0 :=
  (NullSectorTask20.h3_self_eq_zero_iff x).1 h

/-! ## The minimal orientation datum (item 17) -/

/-- **NEWLY DEFINED (item 17).**  The minimal intrinsic orientation datum on `E`: the
inherited spatial triple product.  Only its sign is used below. -/
def triple (p q r : E) : ℝ := h3 (spCross p q) r

theorem triple_apply (p q r : E) :
    triple p q r =
      (p.2.1 * q.2.2 - p.2.2 * q.2.1) * r.1 + (p.2.2 * q.1 - p.1 * q.2.2) * r.2.1
        + (p.1 * q.2.1 - p.2.1 * q.1) * r.2.2 := by
  simp only [triple, h3, dot3, spCross]

/-! ## Coordinates and the matrix of an ordered triple -/

/-- **NEUTRAL DEFINITION.**  The matrix whose three columns are the coordinate vectors of an
ordered triple of elements of `E`. -/
def mat3 (f : Fin 3 → E) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => vc (f j) i

@[simp] theorem mat3_apply (f : Fin 3 → E) (i j : Fin 3) : mat3 f i j = vc (f j) i := rfl

theorem mat3_col (f : Fin 3 → E) (j : Fin 3) : (fun i => mat3 f i j) = vc (f j) := rfl

/-- **DERIVED.**  The determinant of that matrix is exactly the orientation datum. -/
theorem det_mat3 (f : Fin 3 → E) : (mat3 f).det = triple (f 0) (f 1) (f 2) := by
  rw [Matrix.det_fin_three]
  simp only [mat3_apply, vc, triple_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem transpose_mul_mat3 (f : Fin 3 → E) (j k : Fin 3) :
    ((mat3 f)ᵀ * mat3 f) j k = h3 (f j) (f k) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, mat3_apply, Fin.sum_univ_three,
    h3, dot3, vc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-! ## The visible action on `E` -/

/-- **PACKAGED (item 14).**  The inherited visible action of the visible carrier on the
spatial carrier. -/
noncomputable def gact (g : Gvis) (p : E) : E :=
  spatAct ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) p

theorem gact_mem (g : Gvis) : (((g : (Module.End ℝ W)ˣ) : Module.End ℝ W)) ∈ visImage := g.2

@[simp] theorem gact_one (p : E) : gact 1 p = p := by
  have h : (((1 : Gvis) : (Module.End ℝ W)ˣ) : Module.End ℝ W) = LinearMap.id := rfl
  rw [gact, h, spatAct_one, LinearMap.id_apply]

theorem gact_mul (g g' : Gvis) (p : E) : gact (g * g') p = gact g (gact g' p) := by
  have h : (((g * g' : Gvis) : (Module.End ℝ W)ˣ) : Module.End ℝ W)
      = (((g : (Module.End ℝ W)ˣ) : Module.End ℝ W)).comp
        (((g' : (Module.End ℝ W)ˣ) : Module.End ℝ W)) := rfl
  rw [gact, h, spatAct_comp (gact_mem g) (gact_mem g')]
  rfl

theorem gact_add (g : Gvis) (p q : E) : gact g (p + q) = gact g p + gact g q :=
  map_add _ p q

theorem gact_smul (g : Gvis) (c : ℝ) (p : E) : gact g (c • p) = c • gact g p :=
  map_smul _ c p

/-- **INHERITED THEOREM (item 14).**  The visible action preserves the inherited inner
product. -/
theorem gact_ip (g : Gvis) (p q : E) : h3 (gact g p) (gact g q) = h3 p q :=
  spatAct_preserves_inner (gact_mem g) p q

theorem vc_gact (g : Gvis) (p : E) :
    vc (gact g p) = rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) *ᵥ vc p :=
  (rotMat_mulVec _ p).symm

theorem rotMat_mul_mat3 (g : Gvis) (f : Fin 3 → E) :
    rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) * mat3 f
      = mat3 fun i => gact g (f i) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) * mat3 f) i j
      = (rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) *ᵥ (fun k => mat3 f k j)) i := rfl
  rw [h1, mat3_col, ← vc_gact]
  rfl

/-- **DERIVED (item 14).**  The visible action preserves the orientation datum.  This is
derived from the inherited determinant theorem, not assumed. -/
theorem gact_triple (g : Gvis) (p q r : E) :
    triple (gact g p) (gact g q) (gact g r) = triple p q r := by
  have h := congrArg Matrix.det (rotMat_mul_mat3 g ![p, q, r])
  rw [Matrix.det_mul, rotMat_det (gact_mem g), one_mul, det_mat3, det_mat3] at h
  simpa using h.symm

end NullSectorTask24
