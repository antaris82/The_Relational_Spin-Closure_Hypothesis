import Mathlib

/-!
# Task 26, Package A: the varying metric-oriented rank-three input

**Hard target A.**

This module fixes, once and for all, what a *family of real three-dimensional
metric-oriented fibres over a base* is, and nothing more.

The layer is deliberately independent of the earlier one-fibre layers as far as its
*mathematics* is concerned: the completed Task-XXV endpoint is imported unchanged (item 1)
in the final comparison module, and is never used as an input to the definitions below.

## What is defined here

* a small *single-space* layer: for a real inner-product space `V` together with an
  orientation datum `o : Orientation ℝ V (Fin 3)`, the notions used fibrewise later
  (`IsOrientationPreserving`, orientation transport lemmas);
* the input record `MetricOrientedRankThreeFamily B E` (items 21–33): rank exactly three and
  a fibrewise orientation datum, on top of the ambient fibrewise real inner-product
  structure.  It contains **no** trivialization, **no** frame, **no** transition function,
  **no** group action and **no** lifted fibre;
* the fixed metric-oriented model carrier `Model` (used only from Package F onwards);
* the Package-B dependency audit: explicit negative controls showing that the fields of the
  record are logically independent of each other.

## What is *not* here

No vector bundle, no principal bundle, no local triviality (that is additional structure,
introduced only in Package F), no topology on any total space, no spin structure.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

/-! ## Single-space layer: orientation transport -/

section OneSpace

variable {M N P : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [AddCommGroup P] [Module ℝ P]

/-- **DERIVED.**  Transport of an orientation datum along a composite linear equivalence. -/
theorem orientation_map_trans (f : M ≃ₗ[ℝ] N) (g : N ≃ₗ[ℝ] P) (x : Orientation ℝ M (Fin 3)) :
    Orientation.map (Fin 3) (f ≪≫ₗ g) x
      = Orientation.map (Fin 3) g (Orientation.map (Fin 3) f x) := by
  induction x using Module.Ray.ind with
  | h w hw =>
    rw [Orientation.map_apply, Orientation.map_apply, Orientation.map_apply]
    congr 1

/-- **DERIVED.**  The identity transports an orientation datum to itself. -/
theorem orientation_map_refl (x : Orientation ℝ M (Fin 3)) :
    Orientation.map (Fin 3) (LinearEquiv.refl ℝ M) x = x := by
  simp

end OneSpace

/-! ## Single-space layer: orientation-preserving linear isometries -/

section Isom

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **NEWLY DEFINED.**  A linear isometry `V ≃ₗᵢ[ℝ] W` is orientation preserving for the two
orientation data `oV`, `oW` when it transports `oV` to `oW`.  This is the minimal fibrewise
orientation comparison used everywhere below; note that it mentions no frame. -/
def IsOrientationPreserving (oV : Orientation ℝ V (Fin 3)) (oW : Orientation ℝ W (Fin 3))
    (f : V ≃ₗᵢ[ℝ] W) : Prop :=
  Orientation.map (Fin 3) f.toLinearEquiv oV = oW

theorem isOrientationPreserving_refl (oV : Orientation ℝ V (Fin 3)) :
    IsOrientationPreserving oV oV (LinearIsometryEquiv.refl ℝ V) := by
  have h : (LinearIsometryEquiv.refl ℝ V).toLinearEquiv = LinearEquiv.refl ℝ V := rfl
  rw [IsOrientationPreserving, h, orientation_map_refl]

theorem IsOrientationPreserving.symm {oV : Orientation ℝ V (Fin 3)}
    {oW : Orientation ℝ W (Fin 3)} {f : V ≃ₗᵢ[ℝ] W} (hf : IsOrientationPreserving oV oW f) :
    IsOrientationPreserving oW oV f.symm := by
  have h : Orientation.map (Fin 3) f.toLinearEquiv oV = oW := hf
  have h2 : Orientation.map (Fin 3) f.symm.toLinearEquiv
      (Orientation.map (Fin 3) f.toLinearEquiv oV)
      = Orientation.map (Fin 3) f.symm.toLinearEquiv oW := by rw [h]
  rw [← orientation_map_trans] at h2
  have hid : (f.toLinearEquiv ≪≫ₗ f.symm.toLinearEquiv) = LinearEquiv.refl ℝ V := by
    ext x; simp
  rw [hid, orientation_map_refl] at h2
  exact h2.symm

theorem IsOrientationPreserving.trans {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] {oV : Orientation ℝ V (Fin 3)} {oW : Orientation ℝ W (Fin 3)}
    {oU : Orientation ℝ U (Fin 3)} {f : V ≃ₗᵢ[ℝ] W} {g : W ≃ₗᵢ[ℝ] U}
    (hf : IsOrientationPreserving oV oW f) (hg : IsOrientationPreserving oW oU g) :
    IsOrientationPreserving oV oU (f.trans g) := by
  have h : Orientation.map (Fin 3) (f.toLinearEquiv ≪≫ₗ g.toLinearEquiv) oV = oU := by
    rw [orientation_map_trans, hf]; exact hg
  exact h

end Isom

/-! ## The input record (items 21–33) -/

/-- **NEWLY DEFINED (items 21–33), principal.**  A *family of real three-dimensional
metric-oriented fibres over the base `B`*.

The fibre assignment `E : B → Type _` carries, as ambient hypotheses, the fibrewise real
vector-space structure and the fibrewise positive-definite symmetric bilinear form (packaged
in the standard Lean way as `NormedAddCommGroup` + `InnerProductSpace ℝ`).  The record itself
adds exactly two things:

* `rank_three`: every fibre has dimension exactly three;
* `orient`: every fibre carries an orientation datum.

It contains no chosen trivialization, no chosen frame, no transition function, no group
action and no lifted fibre.  The base carries no topology, no manifold structure and no
connectivity assumption. -/
structure MetricOrientedRankThreeFamily (B : Type u) (E : B → Type v)
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] where
  /-- Every fibre is three-dimensional. -/
  rank_three : ∀ b : B, finrank ℝ (E b) = 3
  /-- Every fibre carries an orientation datum. -/
  orient : ∀ b : B, Orientation ℝ (E b) (Fin 3)

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **DERIVED.**  Rank exactly three forces finite-dimensionality of each fibre; this is the
only place where the numeric rank condition is converted into an instance. -/
theorem finiteDimensional (F : MetricOrientedRankThreeFamily B E) (b : B) :
    FiniteDimensional ℝ (E b) := by
  have h : 0 < finrank ℝ (E b) := by rw [F.rank_three b]; norm_num
  exact Module.finite_of_finrank_pos h

/-- **DERIVED.**  Restatement of the rank condition in the form required by the orientation
API (`Fintype.card (Fin 3) = finrank ℝ (E b)`). -/
theorem card_eq_finrank (F : MetricOrientedRankThreeFamily B E) (b : B) :
    Fintype.card (Fin 3) = finrank ℝ (E b) := by
  rw [F.rank_three b]; simp

end MetricOrientedRankThreeFamily

/-! ## The fixed metric-oriented model carrier

`Model` is used **only** from Package F onwards, as the target of a local trivialization.  It
is not a preferred copy of any fibre, and no fibre is assumed equal to it. -/

/-- **NEWLY DEFINED.**  The fixed three-dimensional metric model carrier. -/
abbrev Model : Type := EuclideanSpace ℝ (Fin 3)

/-- **NEWLY DEFINED.**  The fixed orientation datum of the model carrier, given by its
standard orthonormal basis. -/
noncomputable def modelOrient : Orientation ℝ Model (Fin 3) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation

theorem model_rank_three : finrank ℝ Model = 3 := finrank_euclideanSpace_fin

/-! ## Package B — dependency audit by negative controls (items 34–37) -/

section NegativeControls

/-- **NEGATIVE CONTROL (item 36).**  Dimension three together with the metric does *not*
choose an orientation: the model carrier admits two distinct orientation data. -/
theorem exists_two_orientations :
    ∃ o₁ o₂ : Orientation ℝ Model (Fin 3), o₁ ≠ o₂ :=
  ⟨modelOrient, -modelOrient, Module.Ray.ne_neg_self modelOrient⟩

/-- **NEGATIVE CONTROL (item 36).**  Consequently, on one and the same fibre assignment with
one and the same fibrewise metric there are two *different* metric-oriented rank-three family
structures: the metric does not choose the orientation. -/
theorem exists_two_families (B : Type) :
    ∃ F₁ F₂ : MetricOrientedRankThreeFamily B (fun _ : B => Model),
      ∀ b : B, F₁.orient b ≠ F₂.orient b :=
  ⟨⟨fun _ => model_rank_three, fun _ => modelOrient⟩,
    ⟨fun _ => model_rank_three, fun _ => -modelOrient⟩,
    fun _ => Module.Ray.ne_neg_self modelOrient⟩

/-- A three-cycle of `Fin 3`, used only to produce a second positively oriented orthonormal
basis of the model carrier. -/
def cyc3 : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 1 2)

theorem det_cyc3_pos : (0:ℝ) < (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    (⇑(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis ∘ cyc3) := by
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp [Basis.toMatrix_apply, cyc3, Equiv.swap_apply_def, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply]

/-- **DERIVED.**  Reindexing the standard orthonormal basis of the model by the three-cycle
gives a second orthonormal basis with the *same* orientation. -/
theorem reindex_cyc3_orientation :
    ((EuclideanSpace.basisFun (Fin 3) ℝ).reindex cyc3).toBasis.orientation = modelOrient := by
  rw [OrthonormalBasis.reindex_toBasis, modelOrient, Basis.orientation_eq_iff_det_pos,
    Basis.det_reindex]
  exact det_cyc3_pos

/-- **NEGATIVE CONTROL (item 36).**  An orientation does not choose a frame: the model
carrier has two distinct positively oriented orthonormal bases. -/
theorem exists_two_oriented_orthonormal_bases :
    ∃ v w : OrthonormalBasis (Fin 3) ℝ Model,
      v.toBasis.orientation = modelOrient ∧ w.toBasis.orientation = modelOrient ∧ v ≠ w := by
  refine ⟨EuclideanSpace.basisFun (Fin 3) ℝ, (EuclideanSpace.basisFun (Fin 3) ℝ).reindex cyc3,
    rfl, reindex_cyc3_orientation, ?_⟩
  intro h
  have h0 := congrArg (fun v : OrthonormalBasis (Fin 3) ℝ Model => v 0 0) h
  simp [OrthonormalBasis.reindex_apply, cyc3, Equiv.swap_apply_def,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply] at h0

/-- **NEGATIVE CONTROL (item 36).**  A datum at one base point does not choose the data at
other base points: on a two-point base the orientation datum can be prescribed
independently at the two points. -/
theorem pointwise_data_not_global :
    ∃ o : Bool → Orientation ℝ Model (Fin 3),
      o false = modelOrient ∧ o true ≠ modelOrient := by
  refine ⟨fun b => if b then -modelOrient else modelOrient, by simp, ?_⟩
  simpa using (Module.Ray.ne_neg_self modelOrient).symm

end NegativeControls

end NullSectorTask26
