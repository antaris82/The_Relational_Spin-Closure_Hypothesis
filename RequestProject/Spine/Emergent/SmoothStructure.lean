import RequestProject.Spine.Emergent.SmoothGate

/-!
# Spine / Emergent : the smooth-manifold closure of the emergent base

**Seventh module of the manifold-emergence layer (Task 33, §§3–5).**

Task 32 stopped at the *change-of-chart law*: for a base-gluing datum `B` the coordinate
changes of the reconstructed atlas are the primitive identification maps `φ_ij`, and
`BaseGluingData.SmoothGluing` demands that these be smooth.  It did **not** connect this to
Mathlib's manifold predicate.  This module closes that gap for the **actual** Task-32 atlas,
without substituting a new atlas:

* `EmergentBase.BaseGluingData.pieceChart` — the chart attached to an *index* `i` together
  with a witness that the piece `D i` is inhabited.  It is not a new chart: the Task-32
  `chartOfPoint p` is *definitionally* `pieceChart` at the index of the chosen
  representative (`chartOfPoint_eq_pieceChart`), which is exactly the point where the
  quotient's representative selection has to be accounted for.
* `EmergentBase.BaseGluingData.pieceChart_source`, `pieceChart_target`, `pieceChart_apply`,
  `pieceChart_symm_apply` — the concrete description of these charts.
* `EmergentBase.BaseGluingData.transition_source`,
  `EmergentBase.BaseGluingData.transition_apply` — the identification of the coordinate
  change `e.symm ≫ₕ e'` of two atlas members: its source is *exactly* the incidence domain
  `W i j` and on it the map is *exactly* the primitive `φ i j`.  This is the theorem-level
  bridge missing from Task 32.
* `EmergentBase.BaseGluingData.hasGroupoid_of_smoothGluing`,
  `EmergentBase.BaseGluingData.isManifold_of_smoothGluing` — consequently `SmoothGluing`
  *is* sufficient: the reconstructed charted space is a `C^∞` manifold over the local model
  in the sense of Mathlib (Task-33 Outcome A for the smooth gate).
* `EmergentBase.BaseGluingData.smoothEmergentManifoldCertificate` — the full package:
  Hausdorff, second countable, charted, smooth, four-dimensional.

**Negative control.**  Smoothness is *not* automatic: `SmoothGluing` is a hypothesis of
every positive statement here, and `EmergentBase.nonSmoothGluing` is an explicit
base-gluing datum over the local model which violates it
(`EmergentBase.not_smoothGluing_nonSmoothGluing`) while still admitting the whole Task-32
*topological* reconstruction.  So the smooth gate is a genuine extra condition on the
primitive and cannot be read off the topological reconstruction.

**What is deliberately not claimed.**  The converse of
`isManifold_of_smoothGluing` is *not* asserted.  The reconstructed atlas is indexed by the
representatives that `Quotient.out` selects, so it need not contain the chart of every
index `i`; a datum with non-smooth `φ_ij` can therefore still have a smooth reconstructed
atlas (for instance if all selected representatives carry one and the same index).
`SmoothGluing` is proved *sufficient*, and is not claimed necessary.

Nothing about tangent bundles, solder forms, frames, `w₁`, `w₂`, connections or curvature
occurs here, and the import closure of this module is `Mathlib` together with the E1 core
and the `Emergent` modules `LocalModel`, `BaseGluing`, `Reconstruction`, `Symmetric`,
`SmoothGate`.
-/

noncomputable section

namespace EmergentBase

universe u t

namespace BaseGluingData

section Charts

variable {V : Type u} [TopologicalSpace V] {ι : Type t} (B : BaseGluingData V ι)

/-- **REGISTERED (Task 33).**  The Task-32 charted-space structure of the emergent base,
made available to instance resolution.  It is *the* Task-32 structure `B.chartedSpace`; no
second atlas is introduced anywhere in this layer. -/
instance instChartedSpaceSpace (B : BaseGluingData V ι) : ChartedSpace V (Space B) :=
  B.chartedSpace

/-- **NEWLY DEFINED (Task 33).**  The chart of the emergent base attached to an *index* `i`
of the primitive (together with a witness that the piece is inhabited, which the underlying
Mathlib construction needs in order to invert an open embedding).

This is not a new chart: `chartOfPoint p` of Task 32 is definitionally `pieceChart` at the
index of the representative `Quotient.out p`, see `chartOfPoint_eq_pieceChart`. -/
def pieceChart (B : BaseGluingData V ι) (i : ι) (hne : Nonempty (B.D i : Set V)) :
    OpenPartialHomeomorph (Space B) V :=
  haveI := hne
  ((B.isOpenEmbedding_chart i).toOpenPartialHomeomorph _).symm.trans
    (((B.isOpen_D i).isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _)

/-- **DERIVED (Task 33), the representative-selection bookkeeping.**  The Task-32 chart at a
point of the emergent base is the `pieceChart` of the index carried by the representative
selected by the quotient machinery. -/
theorem chartOfPoint_eq_pieceChart (p : Space B) :
    B.chartOfPoint p =
      B.pieceChart (Quotient.out (s := B.setoid) p).1 ⟨(Quotient.out (s := B.setoid) p).2⟩ :=
  rfl

/-- Every member of the Task-32 atlas is a `pieceChart`. -/
theorem exists_pieceChart_of_mem_atlas {e : OpenPartialHomeomorph (Space B) V}
    (he : e ∈ (B.chartedSpace).atlas) : ∃ (i : ι) (hne : Nonempty (B.D i : Set V)),
      e = B.pieceChart i hne := by
  obtain ⟨p, rfl⟩ := he
  exact ⟨_, _, B.chartOfPoint_eq_pieceChart p⟩

variable {B}

@[simp] theorem pieceChart_source {i : ι} (hne : Nonempty (B.D i : Set V)) :
    (B.pieceChart i hne).source = B.chartRange i := by
  simp [pieceChart, chartRange]

@[simp] theorem pieceChart_target {i : ι} (hne : Nonempty (B.D i : Set V)) :
    (B.pieceChart i hne).target = B.D i := by
  simp [pieceChart]

@[simp] theorem pieceChart_apply {i : ι} (hne : Nonempty (B.D i : Set V))
    (x : (B.D i : Set V)) : B.pieceChart i hne (B.chart i x) = (x : V) := by
  haveI := hne
  change (Subtype.val : ↥(B.D i) → V)
      (((B.isOpenEmbedding_chart i).toOpenPartialHomeomorph _).symm (B.chart i x)) = (x : V)
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

@[simp] theorem pieceChart_symm_apply {i : ι} (hne : Nonempty (B.D i : Set V)) {y : V}
    (hy : y ∈ B.D i) : (B.pieceChart i hne).symm y = B.chart i ⟨y, hy⟩ := by
  haveI := hne
  change ((B.isOpenEmbedding_chart i).toOpenPartialHomeomorph _)
      ((((B.isOpen_D i).isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _).symm y)
      = B.chart i ⟨y, hy⟩
  have hval : ((((B.isOpen_D i).isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph
      (Subtype.val : ↥(B.D i) → V)).symm y) = (⟨y, hy⟩ : ↥(B.D i)) := by
    have := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (f := (Subtype.val : ↥(B.D i) → V))
      (h := (B.isOpen_D i).isOpenEmbedding_subtypeVal) (x := ⟨y, hy⟩)
    simpa using this
  rw [hval]
  rfl

/-! ## The coordinate changes of the actual atlas -/

/-- **DERIVED (Task 33), PRINCIPAL — the source of a coordinate change.**  The coordinate
change from the chart of the piece `i` to the chart of the piece `j` is defined exactly on
the incidence domain `W i j` of the primitive. -/
theorem transition_source {i j : ι} (hi : Nonempty (B.D i : Set V))
    (hj : Nonempty (B.D j : Set V)) :
    ((B.pieceChart i hi).symm.trans (B.pieceChart j hj)).source = B.W i j := by
  ext y
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    pieceChart_source, pieceChart_target, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hy, hy'⟩
    rw [pieceChart_symm_apply hi hy] at hy'
    exact (B.mem_chartRange_inter_iff i j ⟨y, hy⟩).1 hy'
  · intro hy
    refine ⟨B.W_subset i j hy, ?_⟩
    rw [pieceChart_symm_apply hi (B.W_subset i j hy)]
    exact (B.mem_chartRange_inter_iff i j ⟨y, B.W_subset i j hy⟩).2 hy

/-- **DERIVED (Task 33), PRINCIPAL — the value of a coordinate change.**  On the incidence
domain the coordinate change between two charts of the reconstructed atlas *is* the
primitive identification map `φ i j`.  No other transition map occurs. -/
theorem transition_apply {i j : ι} (hi : Nonempty (B.D i : Set V))
    (hj : Nonempty (B.D j : Set V)) {y : V} (hy : y ∈ B.W i j) :
    ((B.pieceChart i hi).symm.trans (B.pieceChart j hj)) y = B.φ i j y := by
  have hyD : y ∈ B.D i := B.W_subset i j hy
  show B.pieceChart j hj ((B.pieceChart i hi).symm y) = B.φ i j y
  rw [pieceChart_symm_apply hi hyD, B.chart_eq_chart_of_mem_W i j hy,
    pieceChart_apply hj ⟨B.φ i j y, B.W_subset j i (B.φ_mapsTo i j hy)⟩]

end Charts

/-! ## The smooth gate -/

section Smooth

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **DERIVED (Task 33), PRINCIPAL — every coordinate change of the reconstructed atlas is
smooth.**  This is the statement that Task 32 did *not* prove: it is about the charts that
the reconstructed `ChartedSpace` actually produces, not about the primitive maps alone. -/
theorem contDiffOn_transition (h : B.SmoothGluing) {i j : ι}
    (hi : Nonempty (B.D i : Set LocalModel)) (hj : Nonempty (B.D j : Set LocalModel)) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((B.pieceChart i hi).symm.trans (B.pieceChart j hj))
      ((B.pieceChart i hi).symm.trans (B.pieceChart j hj)).source := by
  rw [transition_source hi hj]
  exact (h i j).congr fun y hy => transition_apply hi hj hy

/-- **DERIVED (Task 33), PRINCIPAL — the smooth gate is closed.**  A smooth base-gluing
datum makes the Task-32 reconstructed charted space a `C^∞` manifold over the local model,
in Mathlib's sense.  The charted-space structure is the Task-32 one, `B.chartedSpace`; no
second atlas is introduced. -/
theorem isManifold_of_smoothGluing (h : B.SmoothGluing) :
    IsManifold (modelWithCornersSelf ℝ LocalModel) (⊤ : ℕ∞) (Space B) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  intro e e' he he'
  obtain ⟨i, hi, rfl⟩ := B.exists_pieceChart_of_mem_atlas he
  obtain ⟨j, hj, rfl⟩ := B.exists_pieceChart_of_mem_atlas he'
  simpa [Function.comp_def] using contDiffOn_transition h hi hj

/-- **DERIVED (Task 33).**  The `HasGroupoid` form of the same statement: the reconstructed
atlas takes values in the `C^∞` structure groupoid of the local model. -/
theorem hasGroupoid_of_smoothGluing (h : B.SmoothGluing) :
    HasGroupoid (Space B) (contDiffGroupoid (⊤ : ℕ∞) (modelWithCornersSelf ℝ LocalModel)) :=
  (isManifold_of_smoothGluing h).toHasGroupoid


/-- **DERIVED (Task 33), PRINCIPAL — the smooth emergent-manifold certificate.**  Under the
already explicit Task-32 conditions — closed gluing graph, countable index type — together
with the Task-32 smoothness condition on the primitive, the emergent base is

1. Hausdorff, 2. second countable, 3. charted over the local model,
4. a `C^∞` manifold over it in Mathlib's sense, and
5. modelled on a *four-dimensional* real local model.

Hausdorffness and second countability are kept separate from `IsManifold`, as in Mathlib. -/
theorem smoothEmergentManifoldCertificate [Countable ι] (hclosed : B.ClosedGluingGraph)
    (hsmooth : B.SmoothGluing) :
    T2Space (Space B) ∧ SecondCountableTopology (Space B) ∧
      IsManifold (modelWithCornersSelf ℝ LocalModel) (⊤ : ℕ∞) (Space B) ∧
      Module.finrank ℝ LocalModel = 4 ∧
      (∀ i, IsOpen (B.chartRange i)) ∧ (⋃ i, B.chartRange i) = Set.univ :=
  ⟨B.t2Space_of_closedGluingGraph hclosed, B.secondCountableTopology_space,
    isManifold_of_smoothGluing hsmooth, finrank_localModel,
    B.isOpen_chartRange, B.iUnion_chartRange⟩

end Smooth

end BaseGluingData

/-! ## Negative control: the smooth gate is a genuine extra condition -/

section NegativeControl

open BaseGluingData

/-- An auxiliary self-homeomorphism of the local model which is continuous but not
differentiable at the origin: it shifts the spatial part by `|t|`. -/
def absShift (x : LocalModel) : LocalModel := (x.1, fun k => |x.1| + x.2 k)

/-- The inverse of `EmergentBase.absShift`. -/
def absShiftInv (x : LocalModel) : LocalModel := (x.1, fun k => x.2 k - |x.1|)

theorem absShiftInv_absShift (x : LocalModel) : absShiftInv (absShift x) = x := by
  ext k <;> simp [absShift, absShiftInv]

theorem absShift_absShiftInv (x : LocalModel) : absShift (absShiftInv x) = x := by
  ext k <;> simp [absShift, absShiftInv]

theorem continuous_absShift : Continuous absShift := by
  refine continuous_fst.prodMk (continuous_pi fun k => ?_)
  exact (continuous_abs.comp continuous_fst).add ((continuous_apply k).comp continuous_snd)

theorem continuous_absShiftInv : Continuous absShiftInv := by
  refine continuous_fst.prodMk (continuous_pi fun k => ?_)
  exact ((continuous_apply k).comp continuous_snd).sub (continuous_abs.comp continuous_fst)

/-- The identification maps of the negative-control datum: the identity on the diagonal,
`absShift` and its inverse off it. -/
def nonSmoothTransition : Bool → Bool → LocalModel → LocalModel
  | false, true => absShift
  | true, false => absShiftInv
  | _, _ => id

/-- **NEWLY DEFINED (Task 33), the negative-control datum.**  A base-gluing datum over the
local model whose identification maps are homeomorphisms but are *not* smooth: two pieces,
both the whole local model, glued by `absShift`. -/
def nonSmoothGluing : BaseGluingData LocalModel Bool where
  D _ := Set.univ
  isOpen_D _ := isOpen_univ
  W _ _ := Set.univ
  isOpen_W _ _ := isOpen_univ
  W_subset _ _ := subset_rfl
  W_self _ := rfl
  φ := nonSmoothTransition
  continuousOn_φ i j := by
    cases i <;> cases j <;>
      simp only [nonSmoothTransition] <;>
      first
        | exact continuousOn_id
        | exact continuous_absShift.continuousOn
        | exact continuous_absShiftInv.continuousOn
  φ_mapsTo _ _ := Set.mapsTo_univ _ _
  φ_self i _ _ := by cases i <;> rfl
  φ_inv i j x _ := by
    cases i <;> cases j <;>
      simp [nonSmoothTransition, absShiftInv_absShift, absShift_absShiftInv]
  φ_cocycle i j k x _ _ := by
    refine ⟨trivial, ?_⟩
    cases i <;> cases j <;> cases k <;>
      simp [nonSmoothTransition, absShiftInv_absShift, absShift_absShiftInv]

@[simp] theorem nonSmoothGluing_φ_false_true :
    nonSmoothGluing.φ false true = absShift := rfl

@[simp] theorem nonSmoothGluing_W (i j : Bool) : nonSmoothGluing.W i j = Set.univ := rfl

/-- `absShift` is not differentiable at the origin, because its second component reproduces
the absolute value. -/
theorem not_differentiableAt_absShift : ¬ DifferentiableAt ℝ absShift 0 := by
  intro h
  have hline : DifferentiableAt ℝ (fun t : ℝ => ((t, 0) : LocalModel)) 0 :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have h0 : DifferentiableAt ℝ absShift ((fun t : ℝ => ((t, 0) : LocalModel)) 0) := by
    simpa using h
  have hproj : ∀ y : LocalModel, DifferentiableAt ℝ (fun x : LocalModel => x.2 0) y :=
    fun _ => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))).differentiableAt
  have hcomp1 : DifferentiableAt ℝ (fun t : ℝ => absShift ((t, 0) : LocalModel)) 0 :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := absShift)
      (f := fun t : ℝ => ((t, 0) : LocalModel)) 0 h0 hline
  have hcomp : DifferentiableAt ℝ
      (fun t : ℝ => (absShift ((t, 0) : LocalModel)).2 0) 0 :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := fun x : LocalModel => x.2 0)
      (f := fun t : ℝ => absShift ((t, 0) : LocalModel)) 0 (hproj _) hcomp1
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    simpa [absShift] using hcomp
  exact not_differentiableAt_abs_zero habs

/-- **DERIVED (Task 33), the negative control.**  The datum `nonSmoothGluing` does *not*
satisfy the smooth gate.  Hence `SmoothGluing` is a genuine additional condition on the
primitive: it is not implied by the Task-32 topological reconstruction, which applies to
this datum verbatim. -/
theorem not_smoothGluing_nonSmoothGluing : ¬ nonSmoothGluing.SmoothGluing := by
  intro h
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) absShift Set.univ := by
    simpa using h false true
  have hdiff : DifferentiableAt ℝ absShift 0 := by
    have := (hcd.differentiableOn (by simp)) 0 (Set.mem_univ _)
    simpa [differentiableWithinAt_univ] using this
  exact not_differentiableAt_absShift hdiff

/-- **DERIVED (Task 33), the negative control, topological side.**  The very same datum
still carries the entire Task-32 *topological* reconstruction: a charted space over the
local model with open, covering chart images.  Topological reconstruction therefore does
not imply the smooth gate. -/
theorem nonSmoothGluing_topological_reconstruction :
    Nonempty (ChartedSpace LocalModel (Space nonSmoothGluing)) ∧
      (∀ i, IsOpen (nonSmoothGluing.chartRange i)) ∧
      (⋃ i, nonSmoothGluing.chartRange i) = Set.univ :=
  ⟨⟨nonSmoothGluing.chartedSpace⟩, nonSmoothGluing.isOpen_chartRange,
    nonSmoothGluing.iUnion_chartRange⟩

end NegativeControl

end EmergentBase

end
