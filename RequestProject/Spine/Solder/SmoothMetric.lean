import RequestProject.Spine.Solder.BundleEquivalence

/-!
# Spine / Solder : the transported Lorentz metric is *smooth*

**Fourth module of the Task-35 regularity layer (Task 35 §7).**

Task 34 transported the intrinsic form `B_𝒮` of the Clifford/Spin core to the tangent fibres
through a weak solder datum and proved the *fibrewise* statements: bilinearity,
nondegeneracy, chart independence, the frame isometry, dimension four.  It proved **no**
regularity, and explicitly did not call the resulting object a Lorentz metric.

With the regular solder datum of `RequestProject.Spine.Solder.RegularSolder` the missing
regularity is available.  Since the pinned Mathlib has no pseudo-Riemannian/Lorentzian metric
structure (see `TASK35_AUDIT.md`), the meaning of "smooth metric" is made explicit here, in
the actual Task-33 charts:

`SpinNative.SmoothTangentSolderData.metricCoeff i y u v = B_𝒮 (A i y⁻¹ u) (A i y⁻¹ v)`

is the metric read in the chart of the piece `i`, at the chart coordinate `y`, on tangent
vectors given by their chart components `u`, `v`; and the theorems below are

* `contDiffOn_metricCoeff` — **smoothness**: every local coefficient function
  `y ↦ g_i(y)(u,v)` is `C^∞` on the chart domain `D i`;
* `metricCoeff_symm` — symmetry;
* `metricCoeff_nondegenerate` — nondegeneracy in every chart;
* `metricCoeff_transform` — the exact (0,2)-tensor transformation law under the *genuine*
  tangent transition `D(φ_ij)` of the Task-33 atlas: the coefficient fields of two charts
  agree, so the metric is a well-defined tensor field and not a chart-dependent expression;
* `metricCoeff_timelike`, `metricCoeff_spacelike`, `metricCoeff_signature` — the signature
  `(1,3)` in every solder frame, in the intrinsic form already certified by the E1 core
  (`B_𝒮(x,y) = x₀y₀ - ⟨x,y⟩`);
* `tangentMetric_localFrame` — the link with the Task-34 fibrewise object: the Task-34
  transported form of the *forgotten* weak datum is exactly this coefficient field read
  through the regular frames.

`smooth_tangent_lorentz_metric` packages all of it.

**Status.**  SMOOTH, in the exact sense stated: the coefficient functions are `C^∞` in the
actual charts and transform as a tensor.  No Mathlib `LorentzianMetric` class is claimed,
because there is none in the pinned version; no connection, curvature or torsion occurs.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

/-! ## The intrinsic form as a continuous bilinear map -/

/-- The intrinsic polarized Lorentz form `B_𝒮`, packaged as a continuous bilinear map of the
finite-dimensional local model.  Continuity is automatic in finite dimension; this is not a
new form. -/
def BSclm : LocalModel →L[ℝ] (LocalModel →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (LocalModel →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (LocalModel →L[ℝ] ℝ)).toLinearMap.comp BSbil)

@[simp] theorem BSclm_apply (x y : LocalModel) : BSclm x y = BS x y := rfl

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

namespace SmoothTangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
  (E : SmoothTangentSolderData B S)

/-! ## The local coefficient field -/

/-- **NEWLY DEFINED (Task 35), PRINCIPAL — the metric in the actual chart coordinates.**  The
intrinsic form `B_𝒮` pulled back through the regular solder comparison of the piece `i`: the
coefficient field of the transported Lorentz metric in the chart of that piece. -/
def metricCoeff (i : ι) (y : LocalModel) (u v : LocalModel) : ℝ :=
  BS ((E.A i y).symm u) ((E.A i y).symm v)

/-- **DERIVED (Task 35).**  The metric is symmetric. -/
theorem metricCoeff_symm (i : ι) (y u v : LocalModel) :
    E.metricCoeff i y u v = E.metricCoeff i y v u :=
  BS_symm _ _

/-- **DERIVED (Task 35).**  The metric is nondegenerate in every chart. -/
theorem metricCoeff_nondegenerate (i : ι) (y : LocalModel) {u : LocalModel} (hu : u ≠ 0) :
    ∃ v : LocalModel, E.metricCoeff i y u v ≠ 0 := by
  have hu' : (E.A i y).symm u ≠ 0 := fun hzero => hu (by
    have := congrArg (E.A i y) hzero
    rwa [ContinuousLinearEquiv.apply_symm_apply, map_zero] at this)
  obtain ⟨w, hw⟩ := BS_nondegenerate hu'
  refine ⟨E.A i y w, ?_⟩
  show BS ((E.A i y).symm u) ((E.A i y).symm (E.A i y w)) ≠ 0
  rwa [ContinuousLinearEquiv.symm_apply_apply]

/-- **DERIVED (Task 35), PRINCIPAL — the metric coefficients are `C^∞`.**  This is the
regularity statement that Task 34 could not make: the local coefficient functions of the
transported Lorentz form are smooth on the chart domain of every piece of the emergent
cover. -/
theorem contDiffOn_metricCoeff (i : ι) (u v : LocalModel) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => E.metricCoeff i y u v) (B.D i) := by
  have hsymm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (((E.A i y).symm : LocalModel →L[ℝ] LocalModel))) (B.D i) :=
    E.contDiffOn_A_symm i
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((E.A i y).symm u)) (B.D i) :=
    hsymm.clm_apply contDiffOn_const
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((E.A i y).symm v)) (B.D i) :=
    hsymm.clm_apply contDiffOn_const
  have hbs : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => BSclm ((E.A i y).symm u)) (B.D i) :=
    (BSclm.contDiff.comp_contDiffOn hu)
  exact hbs.clm_apply hv

/-! ## The tensor transformation law -/

/-- **DERIVED (Task 35), PRINCIPAL — the coefficient field is a tensor field.**  Under the
*genuine* tangent transition `D(φ_ij)` of the Task-33 atlas the coefficient fields of two
charts agree: the metric does not depend on the chart, and the smoothness above is therefore
a statement about a global object. -/
theorem metricCoeff_transform (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j)
    (u v : LocalModel) :
    E.metricCoeff j (B.φ i j y) (B.tangentTransitionMap i j y u)
        (B.tangentTransitionMap i j y v)
      = E.metricCoeff i y u v := by
  have hkey : ∀ w : LocalModel,
      (E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y w)
        = projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩)
            ((E.A i y).symm w) := fun w => E.frameChange_symm i j hy w
  show BS ((E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y u))
      ((E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y v)) = _
  rw [hkey u, hkey v, projectedLorentzTransition_BS]
  rfl

/-! ## The signature -/

/-- **DERIVED (Task 35).**  Every regular solder frame is an isometry of the intrinsic form
onto the metric coefficients. -/
theorem metricCoeff_frame_isometry (i : ι) (y a b : LocalModel) :
    E.metricCoeff i y (E.A i y a) (E.A i y b) = BS a b := by
  show BS ((E.A i y).symm (E.A i y a)) ((E.A i y).symm (E.A i y b)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- **DERIVED (Task 35).**  The solder image of the intrinsic unit is a unit timelike vector
for the metric. -/
theorem metricCoeff_timelike (i : ι) (y : LocalModel) :
    E.metricCoeff i y (E.A i y sOne) (E.A i y sOne) = 1 := by
  rw [E.metricCoeff_frame_isometry, BS_eq]
  show (1 : ℝ) * 1 - sip 0 0 = 1
  rw [sip]
  norm_num

/-- **DERIVED (Task 35).**  The solder image of a spatial vector is spacelike, and strictly
so unless it vanishes. -/
theorem metricCoeff_spacelike (i : ι) (y : LocalModel) (w : Fin 3 → ℝ) :
    E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) = - sip w w := by
  rw [E.metricCoeff_frame_isometry, BS_eq]
  show (0 : ℝ) * 0 - sip w w = - sip w w
  ring

/-- **DERIVED (Task 35), PRINCIPAL — the signature is `(1,3)`.**  In every regular solder
frame the metric has one positive direction (the intrinsic unit) and a three-dimensional
negative definite orthogonal complement; this is the intrinsic Lorentz signature of the E1
core, transported. -/
theorem metricCoeff_signature (i : ι) (y : LocalModel) :
    E.metricCoeff i y (E.A i y sOne) (E.A i y sOne) = 1 ∧
    (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y sOne) (E.A i y (0, w)) = 0) ∧
    (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) ≤ 0) ∧
    (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) = 0 → w = 0) := by
  refine ⟨E.metricCoeff_timelike i y, fun w => ?_, fun w => ?_, fun w hw => ?_⟩
  · rw [E.metricCoeff_frame_isometry, BS_eq]
    show (1 : ℝ) * 0 - sip 0 w = 0
    rw [sip]
    norm_num
  · rw [E.metricCoeff_spacelike]
    exact neg_nonpos.2 (sip_self_nonneg w)
  · rw [E.metricCoeff_spacelike] at hw
    exact sip_self_eq_zero (by linarith)

/-! ## The link with the Task-34 fibrewise object -/

/-- **DERIVED (Task 35).**  The Task-34 transported fibrewise form of the *forgotten* weak
datum is exactly this coefficient field, read through the regular solder frames.  So the
Task-34 fibrewise theorems and the Task-35 regularity theorems speak about one and the same
object. -/
theorem tangentMetric_localFrame (h : B.SmoothGluing) (i : ι) {x : Space B}
    (hx : x ∈ B.chartRange i) (a b : LocalModel) :
    (E.toTangentSolderData h).tangentMetric x (E.localFrame h i hx a) (E.localFrame h i hx b)
      = BS a b := by
  have hframe := E.toTangentSolderData_frame h i hx
  have h1 : (E.toTangentSolderData h).tangentMetric x
      ((E.toTangentSolderData h).frame i x a) ((E.toTangentSolderData h).frame i x b)
      = BS a b := (E.toTangentSolderData h).tangentMetric_frame_isometry hx a b
  rw [hframe a, hframe b] at h1
  exact h1

/-- **DERIVED (Task 35), PACKAGED — the smooth Lorentz metric of the emergent manifold.**

From the Clifford/Spin core's intrinsic form `B_𝒮` and a *regular* solder datum alone:

1. the metric coefficient field of every chart is `C^∞` on the chart domain;
2. it is symmetric;
3. it is nondegenerate at every point of every chart;
4. it transforms exactly as a `(0,2)`-tensor under the genuine tangent transitions `D(φ_ij)`
   of the actual Task-33 atlas, hence defines one chart-independent field;
5. its signature is `(1,3)` in every solder frame;
6. it agrees with the Task-34 fibrewise transported form.

No connection, parallel transport, curvature, torsion or dynamics occurs. -/
theorem smooth_tangent_lorentz_metric (h : B.SmoothGluing) :
    (∀ i u v, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => E.metricCoeff i y u v) (B.D i)) ∧
    (∀ i y u v, E.metricCoeff i y u v = E.metricCoeff i y v u) ∧
    (∀ i y, ∀ u ≠ (0 : LocalModel), ∃ v, E.metricCoeff i y u v ≠ 0) ∧
    (∀ i j, ∀ y ∈ B.W i j, ∀ u v,
      E.metricCoeff j (B.φ i j y) (B.tangentTransitionMap i j y u)
          (B.tangentTransitionMap i j y v)
        = E.metricCoeff i y u v) ∧
    (∀ i y, E.metricCoeff i y (E.A i y sOne) (E.A i y sOne) = 1 ∧
      (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) ≤ 0) ∧
      (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) = 0 → w = 0)) ∧
    (∀ (i : ι) (x : Space B) (hx : x ∈ B.chartRange i) (a b : LocalModel),
      (E.toTangentSolderData h).tangentMetric x (E.localFrame h i hx a)
          (E.localFrame h i hx b) = BS a b) :=
  ⟨fun i u v => E.contDiffOn_metricCoeff i u v,
   fun i y u v => E.metricCoeff_symm i y u v,
   fun i y _ hu => E.metricCoeff_nondegenerate i y hu,
   fun i j _ hy u v => E.metricCoeff_transform i j hy u v,
   fun i y => ⟨E.metricCoeff_timelike i y, (E.metricCoeff_signature i y).2.2.1,
     (E.metricCoeff_signature i y).2.2.2⟩,
   fun _ _ hx a b => E.tangentMetric_localFrame h _ hx a b⟩


end SmoothTangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.SmoothTangentSolderData.contDiffOn_metricCoeff
#print axioms SpinNative.SmoothTangentSolderData.metricCoeff_transform
#print axioms SpinNative.SmoothTangentSolderData.metricCoeff_signature
#print axioms SpinNative.SmoothTangentSolderData.smooth_tangent_lorentz_metric
