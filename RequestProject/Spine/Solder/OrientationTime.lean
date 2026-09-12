import RequestProject.Spine.Solder.SmoothMetric

/-!
# Spine / Solder : orientation and time orientation, at their exact regularity level

**Sixth module of the Task-35 regularity layer (Task 35 §8).**

Task 34 produced a "volume form" and a "time field" by choosing, for each point, *some*
index of a covering piece, and proved nothing about their regularity.  Task 35 must instead
separate

* **the reductions** — what the projected transitions actually force, with no pointwise
  choice function anywhere;
* **the chosen representatives** — local, smooth, and glued only under an extra condition.

## Derived: the reductions (choice-free)

* `SpinNative.SmoothTangentSolderData.frameChange_det` — the change between the solder
  comparisons of two charts, conjugated by the genuine tangent transition, has determinant
  `1`.  This is the **orientation reduction**: the solder frames form an oriented family,
  because the projected internal Lorentz transitions lie in the native proper group.
* `SpinNative.SmoothTangentSolderData.futureCone` and
  `SpinNative.SmoothTangentSolderData.futureCone_transform` — the future cone field, defined
  in chart coordinates, is preserved by the genuine tangent transitions: a
  chart-independent field of cones.  This is the **time-orientation reduction**, and it uses
  only orthochronicity of the projected transitions.
* `SpinNative.SmoothTangentSolderData.futureCone_eq_of_mem` — the cone at a point does not
  depend on which chart is used to describe it.

Neither statement mentions a choice function; both are theorems about the two certified
transition systems.

## Chosen representatives: local and smooth, global only conditionally

* `SpinNative.SmoothTangentSolderData.timeField` — the local timelike field
  `T_i(y) = A i y (𝟙_𝒮)`, `C^∞` on the chart domain (`contDiffOn_timeField`) and
  future-directed at every point (`timeField_mem_futureCone`);
* `SpinNative.SmoothTangentSolderData.timeField_glue_iff` — the **exact** obstruction to
  gluing them: the local representatives of two charts agree under the genuine tangent
  transition **iff** the projected internal Lorentz transition fixes the intrinsic unit.  So
  a global smooth representative is *not* forced by the solder;
* `SpinNative.SmoothTangentSolderData.timeField_glue_of_trivial` — for a Spin seed with
  trivial projected transition the local fields do glue, so in that case a global smooth
  future-directed field exists.

**Classification (Task 35 §8).**

```text
orientation reduction                      : DERIVED
time-orientation (cone) reduction          : DERIVED
local smooth timelike representative       : DERIVED
global smooth timelike representative      : ADDITIONAL THEOREM
    (forced only when the projected Lorentz cocycle fixes the intrinsic unit;
     in general it needs a partition of unity / a section of the cone bundle,
     which is not developed here)
```

No claim is made that `x ↦ tangentLinearEquiv (idx x) 𝟙_𝒮` is a smooth global field; the
Task-34 objects built from a choice function are left exactly as fibrewise witnesses.

## CLARIFICATION NOTICE (Task 36 §3) — what `timeField_glue_iff` is *not*

The text above is preserved unchanged and is accurate, but it has been read downstream as if
`SpinNative.SmoothTangentSolderData.timeField_glue_iff` were an obstruction to *time
orientability*.  It is not.  To make the distinction impossible to miss:

* `timeField_glue_iff` is the exact gluing criterion for **one distinguished local
  representative**, namely `T_i(y) = A i y (𝟙_𝒮)`.  Failure of *this particular* family to
  glue says nothing about the existence of *some* global future-directed timelike field, and
  nothing about the existence of the time-orientation reduction.
* The **time-orientation reduction itself is unconditionally derived** from a regular solder.
  Task 36 isolates it as a structure, `Task36.TimeOrientationReduction`, and proves
  `Task36.solder_timeOrientationReduction` /
  `Task36.nonempty_timeOrientationReduction_of_solder`: a regular solder *always* produces a
  coherent smooth future-cone reduction on `TM`, with no hypothesis on the Spin seed.  The
  one-loop model — nontrivial global topology — is a positive control:
  `Task36.loop_timeOrientationReduction_isGlued`.

The honest Task-36 classification is therefore

```text
time-orientation reduction                 : DERIVED
global smooth timelike representative      : ADDITIONAL THEOREM / INFRASTRUCTURE BLOCKER
```

the blocker being a smooth section of a field of open convex cones over a paracompact smooth
manifold (the partition-of-unity argument), which is not developed in the pinned Mathlib for
this project's `VectorBundleCore`-level presentation of `TM`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

namespace SmoothTangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
  (E : SmoothTangentSolderData B S)

/-! ## Orientation reduction -/

/-- **NEWLY DEFINED (Task 35).**  The change of solder comparison between two charts,
conjugated by the genuine tangent transition of the Task-33 atlas: the linear map of the
local model that compares the two regular solder frames over a point of an overlap. -/
def frameChange (i j : ι) (y : LocalModel) : LocalModel →ₗ[ℝ] LocalModel :=
  (((E.A j (B.φ i j y)).symm : LocalModel →L[ℝ] LocalModel).comp
    ((B.tangentTransitionMap i j y).comp
      ((E.A i y : LocalModel →L[ℝ] LocalModel)))).toLinearMap

theorem frameChange_apply (i j : ι) (y w : LocalModel) :
    E.frameChange i j y w = (E.A j (B.φ i j y)).symm
      (B.tangentTransitionMap i j y (E.A i y w)) := rfl

/-- **DERIVED (Task 35).**  The frame change *is* the projected internal Lorentz transition;
no choice and no orientation convention enters. -/
theorem frameChange_eq (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) (w : LocalModel) :
    E.frameChange i j y w
      = projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩) w := by
  rw [frameChange_apply, E.frameChange_symm i j hy, ContinuousLinearEquiv.symm_apply_apply]

/-- **DERIVED (Task 35), the orientation reduction.**  The comparison of two regular solder
frames has determinant `1`: the solder frames of the different charts form a coherently
oriented family.  This is forced by the native Spin projection landing in the proper group
`GLor`, and it involves no choice function. -/
theorem frameChange_det (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) :
    LinearMap.det (E.frameChange i j y) = 1 := by
  have hfun : E.frameChange i j y
      = ((projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩) :
          LocalModel ≃ₗ[ℝ] LocalModel) : LocalModel →ₗ[ℝ] LocalModel) :=
    LinearMap.ext fun w => E.frameChange_eq i j hy w
  rw [hfun]
  exact projectedLorentzTransition_det S j i _

/-! ## Time-orientation reduction: the future cone field -/

/-- **NEWLY DEFINED (Task 35).**  The future cone at a point of the chart `i`, in the chart
components: the vectors whose solder pull-back lies in the intrinsic interior future of the
Clifford core. -/
def futureCone (i : ι) (y : LocalModel) : Set LocalModel :=
  {u : LocalModel | (E.A i y).symm u ∈ IntFuture}

/-- **DERIVED (Task 35), the time-orientation reduction.**  The genuine tangent transition
of the Task-33 atlas carries the future cone of one chart onto the future cone of the other:
the cone field is a chart-independent field, because the projected internal Lorentz
transitions are orthochronous.  No pointwise choice occurs. -/
theorem futureCone_transform (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) (u : LocalModel) :
    u ∈ E.futureCone i y ↔
      B.tangentTransitionMap i j y u ∈ E.futureCone j (B.φ i j y) := by
  have hkey : (E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y u)
      = projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩)
          ((E.A i y).symm u) := E.frameChange_symm i j hy u
  show (E.A i y).symm u ∈ IntFuture ↔
    (E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y u) ∈ IntFuture
  rw [hkey]
  exact projectedLorentzTransition_intFuture S j i _ ((E.A i y).symm u)

/-- **DERIVED (Task 35).**  Equivalently: the solder images of the intrinsic interior future
computed in two charts agree. -/
theorem futureCone_eq_of_mem (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) :
    B.tangentTransitionMap i j y '' E.futureCone i y ⊆ E.futureCone j (B.φ i j y) := by
  rintro u ⟨w, hw, rfl⟩
  exact (E.futureCone_transform i j hy w).1 hw

/-! ## The local smooth timelike representative -/

/-- **NEWLY DEFINED (Task 35).**  The local time field of the chart `i`: the solder image of
the intrinsic unit of the Clifford core, in the chart components. -/
def timeField (i : ι) (y : LocalModel) : LocalModel := E.A i y sOne

/-- **DERIVED (Task 35).**  The local time field is `C^∞` on the chart domain. -/
theorem contDiffOn_timeField (i : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (E.timeField i) (B.D i) :=
  (E.contDiffOn_A i).clm_apply contDiffOn_const

/-- **DERIVED (Task 35).**  The local time field is future-directed at every point of the
chart domain, for the transported metric. -/
theorem timeField_mem_futureCone (i : ι) (y : LocalModel) :
    E.timeField i y ∈ E.futureCone i y := by
  show (E.A i y).symm (E.A i y sOne) ∈ IntFuture
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact one_mem_intFuture

/-- **DERIVED (Task 35).**  Its metric normalization is the intrinsic one. -/
theorem metricCoeff_timeField (i : ι) (y : LocalModel) :
    E.metricCoeff i y (E.timeField i y) (E.timeField i y) = 1 :=
  E.metricCoeff_timelike i y

/-- **DERIVED (Task 35), THE EXACT OBSTRUCTION.**  The local time fields of two charts agree
under the genuine tangent transition **exactly** when the projected internal Lorentz
transition fixes the intrinsic unit.  A *global* smooth timelike representative is therefore
not forced by a regular solder: what is forced is the cone field, not a section of it. -/
theorem timeField_glue_iff (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) :
    B.tangentTransitionMap i j y (E.timeField i y) = E.timeField j (B.φ i j y) ↔
      projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩) sOne = sOne := by
  constructor
  · intro hglue
    have h1 := E.frameChange_symm i j hy (E.A i y sOne)
    rw [ContinuousLinearEquiv.symm_apply_apply] at h1
    show projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩) sOne = sOne
    rw [← h1]
    show (E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y (E.timeField i y)) = sOne
    rw [hglue]
    show (E.A j (B.φ i j y)).symm (E.A j (B.φ i j y) sOne) = sOne
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · intro hfix
    have h1 := E.frameChange_symm i j hy (E.A i y sOne)
    rw [ContinuousLinearEquiv.symm_apply_apply, hfix] at h1
    have := congrArg (E.A j (B.φ i j y)) h1
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this

/-- **DERIVED (Task 35), the positive case.**  If the projected internal Lorentz transition
is trivial then the local smooth time fields do glue along the genuine tangent transitions:
a global smooth future-directed representative exists in that case (and only the general
case is left open). -/
theorem timeField_glue_of_trivial
    (htriv : ∀ (a b : ι) (x : Space B),
      projectedLorentzTransition S a b x = LinearEquiv.refl ℝ LocalModel)
    (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) :
    B.tangentTransitionMap i j y (E.timeField i y) = E.timeField j (B.φ i j y) := by
  refine (E.timeField_glue_iff i j hy).2 ?_
  rw [htriv j i]
  rfl

/-- **DERIVED (Task 35), PACKAGED — orientation and time orientation at the exact regularity
level proved.**

1. **Orientation reduction (DERIVED).**  The comparison of the solder frames of two charts
   has determinant `1`.
2. **Time-orientation reduction (DERIVED).**  The future cone field is preserved by the
   genuine tangent transitions of the actual atlas.
3. **Local smooth representative (DERIVED).**  Each chart carries a `C^∞` future-directed
   unit timelike field.
4. **Global smooth representative (ADDITIONAL THEOREM).**  The local representatives glue
   exactly when the projected Lorentz cocycle fixes the intrinsic unit; no global smooth
   representative is claimed in general.

No arbitrary index-choice function occurs in 1–3. -/
theorem orientation_time_orientation_status :
    (∀ i j, ∀ y ∈ B.W i j, LinearMap.det (E.frameChange i j y) = 1) ∧
    (∀ i j, ∀ y ∈ B.W i j, ∀ u,
      u ∈ E.futureCone i y ↔ B.tangentTransitionMap i j y u ∈ E.futureCone j (B.φ i j y)) ∧
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (E.timeField i) (B.D i)) ∧
    (∀ i y, E.timeField i y ∈ E.futureCone i y ∧
      E.metricCoeff i y (E.timeField i y) (E.timeField i y) = 1) ∧
    (∀ (i j : ι) (y : LocalModel) (hy : y ∈ B.W i j),
      B.tangentTransitionMap i j y (E.timeField i y) = E.timeField j (B.φ i j y) ↔
        projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩) sOne = sOne) :=
  ⟨fun i j _ hy => E.frameChange_det i j hy,
   fun i j _ hy u => E.futureCone_transform i j hy u,
   fun i => E.contDiffOn_timeField i,
   fun i y => ⟨E.timeField_mem_futureCone i y, E.metricCoeff_timeField i y⟩,
   fun i j _ hy => E.timeField_glue_iff i j hy⟩


end SmoothTangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.SmoothTangentSolderData.frameChange_det
#print axioms SpinNative.SmoothTangentSolderData.futureCone_transform
#print axioms SpinNative.SmoothTangentSolderData.contDiffOn_timeField
#print axioms SpinNative.SmoothTangentSolderData.timeField_glue_iff
#print axioms SpinNative.SmoothTangentSolderData.orientation_time_orientation_status
