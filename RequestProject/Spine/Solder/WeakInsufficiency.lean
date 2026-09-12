import RequestProject.Spine.Solder.RegularExamples

/-!
# Spine / Solder : the Task-34 weak solder datum is **not** regular

**Fifth module of the Task-35 regularity layer — the negative control of Task 35 §4.**

Task 34 was explicit that its solder datum `SpinNative.TangentSolderData` imposes no
regularity on the frames.  Task 35 must turn that remark into a theorem, and this module
does so, on an explicit Task-33 emergent manifold.

## The local representative of a weak solder

The object whose regularity is at stake is the *local representative* of the solder frame in
the actual tangent trivialization of the Task-33 atlas:

`SpinNative.weakTangentRep h E i x = D(φ_{k,i})(outCoord x) ∘ E.frame i x`,

where `k` is the index of the Mathlib chart at `x`.  (The tangent fibre of Mathlib's
`tangentBundleCore` at `x` *is* the model vector space, its elements being the components in
that chart; the identification is used here purely as coordinates, never as a solder — cf.
`EmergentBase.tangentSpace_eq_localModel`.)

* `SpinNative.SmoothTangentSolderData.weakTangentRep_eq` — for a *regular* solder the local
  representative is exactly the smooth comparison `A i` (read at the chart coordinate);
* `SpinNative.SmoothTangentSolderData.continuousOn_weakTangentRep` — so it is continuous on
  every chart domain.

## The negative control

On the symmetric canonical Task-33 manifold (one piece, the whole local model, identity
gluing) with the pointwise trivial Spin seed, the weak Task-34 law degenerates to *no
condition at all* on the frame field.  `SpinNative.badSolder` is the weak solder datum whose
frame is the identity everywhere except at one point, where it is the dilation by `2`.  It
satisfies every Task-34 axiom, and

* `SpinNative.badSolder_rep_not_continuousOn` — its local representative is **not**
  continuous;
* `SpinNative.badSolder_metric_not_continuousOn` — the induced fibrewise Task-34 "metric" is
  **not** continuous either, as a coefficient function in the actual chart;
* `SpinNative.weak_solder_not_regular` — consequently **no** regular solder datum induces it:

  > a weak `TangentSolderData` does not imply regular/smooth solder data.

This is the exact theorem-level content of the Task-34 gap, and it is why Task 35 introduces
`SpinNative.SmoothTangentSolderData`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-! ## The local representative of a solder frame in the actual tangent trivialization -/

/-- **NEWLY DEFINED (Task 35).**  The local representative of a (weak) solder frame in the
tangent trivialization attached to the chart of the piece `i`: the frame followed by the
genuine tangent coordinate change from the Mathlib chart at the point to the chart of the
piece `i`.  For a regular solder datum this is exactly the smooth comparison `A i`
(`SmoothTangentSolderData.weakTangentRep_eq`). -/
def weakTangentRep {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
    (E : TangentSolderData B S) (i : ι) (x : Space B) (v : LocalModel) : LocalModel :=
  B.tangentTransitionMap (B.outIndex x) i (B.outCoord x) (E.frame i x v)

namespace SmoothTangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
  (E : SmoothTangentSolderData B S)

/-- **DERIVED (Task 35).**  The local representative of the weak solder underlying a regular
one is the regular comparison itself. -/
theorem weakTangentRep_eq (h : B.SmoothGluing) (i : ι) {x : Space B}
    (hx : x ∈ B.chartRange i) (v : LocalModel) :
    weakTangentRep (E.toTangentSolderData h) i x v = E.A i (B.pieceCoord i x) v := by
  have hik : B.pieceCoord i x ∈ B.W i (B.outIndex x) := B.pieceCoord_mem_W hx
  have hφ : B.φ i (B.outIndex x) (B.pieceCoord i x) = B.outCoord x := by
    rw [B.φ_pieceCoord hx (B.mem_chartRange_outIndex x), B.pieceCoord_outIndex]
  have hinv := BaseGluingData.tangentTransitionMap_left_inv h hik
    (E.A i (B.pieceCoord i x) v)
  rw [hφ] at hinv
  show B.tangentTransitionMap (B.outIndex x) i (B.outCoord x)
      ((E.toTangentSolderData h).frame i x v) = _
  rw [E.toTangentSolderData_frame h i hx v, localFrame_apply]
  exact hinv

/-- **DERIVED (Task 35).**  The local representative of a regular solder is continuous on the
chart domain — this is the property that the weak datum fails to have. -/
theorem continuousOn_weakTangentRep (h : B.SmoothGluing) (i : ι)
    (hi : Nonempty (B.D i : Set LocalModel)) (v : LocalModel) :
    ContinuousOn (fun x => weakTangentRep (E.toTangentSolderData h) i x v)
      (B.chartRange i) := by
  have hA : ContinuousOn (fun y : LocalModel => ((E.A i y : LocalModel →L[ℝ] LocalModel)))
      (B.D i) := (E.contDiffOn_A i).continuousOn
  have hAv : ContinuousOn (fun y : LocalModel => (E.A i y v)) (B.D i) := by
    have := hA.clm_apply (continuousOn_const (c := v))
    exact this
  have hmaps : Set.MapsTo (B.pieceCoord i) (B.chartRange i) (B.D i) :=
    fun x hx => B.pieceCoord_mem_D hx
  refine (hAv.comp (B.continuousOn_pieceCoord i hi) hmaps).congr fun x hx => ?_
  exact E.weakTangentRep_eq h i hx v

end SmoothTangentSolderData

/-! ## The negative control -/

/-- The symmetric canonical Task-33 emergent manifold on one piece: the whole local model,
glued to itself by the identity. -/
abbrev flatBase : BaseGluingData LocalModel Unit :=
  symmetricGluing Unit (isOpen_univ : IsOpen (Set.univ : Set LocalModel))

theorem flatBase_smoothGluing : flatBase.SmoothGluing :=
  symmetricGluing.smoothGluing _

/-- The base point at which the bad frame field jumps. -/
def flatPoint : Space flatBase := flatBase.chart () ⟨0, Set.mem_univ 0⟩

/-- The embedding of the local model as the (single) chart of the flat emergent base. -/
def flatChart (y : LocalModel) : Space flatBase := flatBase.chart () ⟨y, Set.mem_univ y⟩

theorem continuous_flatChart : Continuous flatChart :=
  (flatBase.continuous_chart ()).comp (Continuous.subtype_mk continuous_id _)

theorem flatChart_injective {y z : LocalModel} (hyz : flatChart y = flatChart z) : y = z :=
  congrArg Subtype.val (flatBase.injective_chart () hyz)

theorem flatChart_zero : flatChart 0 = flatPoint := rfl

open Classical in
/-- **NEWLY DEFINED (Task 35), the negative control frame field.**  The identity frame
everywhere except at one point, where it is the dilation by `2`.  It is measurable-free,
choice-free nonsense geometrically — and that is the point: the Task-34 axioms cannot see
it. -/
def badFrameField (x : Space flatBase) : LocalModel ≃ₗ[ℝ] TangentSpace localModelI x :=
  if x = flatPoint then LinearEquiv.smulOfNeZero ℝ LocalModel 2 two_ne_zero
    else LinearEquiv.refl ℝ LocalModel

theorem badFrameField_of_ne {x : Space flatBase} (hx : x ≠ flatPoint) (v : LocalModel) :
    badFrameField x v = v := by
  have : badFrameField x = LinearEquiv.refl ℝ LocalModel := dif_neg hx
  rw [this]
  rfl

theorem badFrameField_at (v : LocalModel) :
    badFrameField flatPoint v = (2 : ℝ) • v := by
  have : badFrameField flatPoint = LinearEquiv.smulOfNeZero ℝ LocalModel 2 two_ne_zero :=
    dif_pos rfl
  rw [this]
  rfl

/-- **NEWLY DEFINED (Task 35), the negative control.**  A weak Task-34 solder datum on the
symmetric canonical emergent manifold whose frame field jumps at one point.  Every Task-34
axiom holds: with the trivial Spin seed the overlap law says only that the frames of two
pieces agree, and there is only one piece. -/
def badSolder : TangentSolderData flatBase
    (trivialCocycle (↥SpinGroup) (emergentCover flatBase)) where
  frame _ x := badFrameField x
  compatibility i j x _ v := by
    rw [projectedLorentzTransition_trivial]
    rfl

/-- **DERIVED (Task 35).**  On the flat base the local representative of the bad solder is
the bad frame field itself: all tangent transitions are the identity there. -/
theorem badSolder_rep (x : Space flatBase) (v : LocalModel) :
    weakTangentRep badSolder () x v = badFrameField x v := by
  show flatBase.tangentTransitionMap (flatBase.outIndex x) () (flatBase.outCoord x)
      (badFrameField x v) = _
  rw [symmetricGluing_tangentTransitionMap (isOpen_univ : IsOpen (Set.univ : Set LocalModel))
    (flatBase.outIndex x) () (Set.mem_univ (flatBase.outCoord x))]
  rfl

/-! ### The jump: the representative and the induced metric are discontinuous -/

theorem badSolder_rep_flatChart_of_ne {y : LocalModel} (hy : y ≠ 0) :
    (weakTangentRep badSolder () (flatChart y) sOne).1 = 1 := by
  have hne : flatChart y ≠ flatPoint := by
    intro hcontra
    exact hy (flatChart_injective (hcontra.trans flatChart_zero.symm))
  rw [badSolder_rep, badFrameField_of_ne hne]
  rfl

theorem badSolder_rep_flatChart_zero :
    (weakTangentRep badSolder () (flatChart 0) sOne).1 = 2 := by
  rw [flatChart_zero, badSolder_rep, badFrameField_at]
  show (2 : ℝ) * 1 = 2
  ring

/-- **DERIVED (Task 35), PRINCIPAL NEGATIVE CONTROL.**  The local representative of the weak
solder datum `badSolder` is not continuous on the chart domain: a weak Task-34 solder datum
carries no regularity whatsoever. -/
theorem badSolder_rep_not_continuousOn :
    ¬ ContinuousOn (fun x => (weakTangentRep badSolder () x sOne).1)
        (flatBase.chartRange ()) := by
  intro hc
  have hcont : Continuous
      (fun y : LocalModel => (weakTangentRep badSolder () (flatChart y) sOne).1) := by
    have huniv : flatBase.chartRange () = Set.univ := by
      exact symmetricGluing.chartRange_eq_univ _ ()
    rw [huniv] at hc
    exact (continuousOn_univ.1 hc).comp continuous_flatChart
  have h2 : Filter.Tendsto
      (fun y : LocalModel => (weakTangentRep badSolder () (flatChart y) sOne).1)
      (nhdsWithin 0 {(0 : LocalModel)}ᶜ) (nhds 2) := by
    have h0 : (2 : ℝ)
        = (fun y : LocalModel => (weakTangentRep badSolder () (flatChart y) sOne).1) 0 :=
      badSolder_rep_flatChart_zero.symm
    rw [h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : Filter.Tendsto
      (fun y : LocalModel => (weakTangentRep badSolder () (flatChart y) sOne).1)
      (nhdsWithin 0 {(0 : LocalModel)}ᶜ) (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (badSolder_rep_flatChart_of_ne hy).symm
  have hval : (2 : ℝ) = 1 := tendsto_nhds_unique h2 h1
  norm_num at hval

/-- **DERIVED (Task 35).**  The fibrewise Task-34 "metric" of the same weak datum is not
continuous either, read as a coefficient function in the actual chart. -/
theorem badSolder_metric_not_continuousOn :
    ¬ Continuous (fun y : LocalModel =>
        BS ((badFrameField (flatChart y)).symm sOne)
          ((badFrameField (flatChart y)).symm sOne)) := by
  intro hcont
  have hzero : BS ((badFrameField (flatChart 0)).symm sOne)
      ((badFrameField (flatChart 0)).symm sOne) = 1 / 4 := by
    have hs : (badFrameField (flatChart 0)).symm sOne = (2 : ℝ)⁻¹ • (sOne : LocalModel) := by
      refine (LinearEquiv.symm_apply_eq _).2 ?_
      rw [flatChart_zero, badFrameField_at]
      rw [smul_smul, mul_inv_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]
    rw [hs, BS_eq]
    show (2 : ℝ)⁻¹ * 1 * ((2 : ℝ)⁻¹ * 1) - sip ((2 : ℝ)⁻¹ • (0 : Fin 3 → ℝ))
      ((2 : ℝ)⁻¹ • (0 : Fin 3 → ℝ)) = 1 / 4
    rw [sip]
    norm_num
  have hne : ∀ y : LocalModel, y ≠ 0 →
      BS ((badFrameField (flatChart y)).symm sOne)
        ((badFrameField (flatChart y)).symm sOne) = 1 := by
    intro y hy
    have hne' : flatChart y ≠ flatPoint := by
      intro hcontra
      exact hy (flatChart_injective (hcontra.trans flatChart_zero.symm))
    have hs : (badFrameField (flatChart y)).symm sOne = (sOne : LocalModel) := by
      refine (LinearEquiv.symm_apply_eq _).2 ?_
      rw [badFrameField_of_ne hne']
    rw [hs, BS_eq]
    show (1 : ℝ) * 1 - sip 0 0 = 1
    rw [sip]
    norm_num
  have h2 : Filter.Tendsto (fun y : LocalModel =>
      BS ((badFrameField (flatChart y)).symm sOne) ((badFrameField (flatChart y)).symm sOne))
      (nhdsWithin 0 {(0 : LocalModel)}ᶜ) (nhds (1 / 4)) := by
    have h0 : (1 / 4 : ℝ) = (fun y : LocalModel =>
        BS ((badFrameField (flatChart y)).symm sOne)
          ((badFrameField (flatChart y)).symm sOne)) 0 := hzero.symm
    rw [h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : Filter.Tendsto (fun y : LocalModel =>
      BS ((badFrameField (flatChart y)).symm sOne) ((badFrameField (flatChart y)).symm sOne))
      (nhdsWithin 0 {(0 : LocalModel)}ᶜ) (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hne y hy).symm
  have hval : (1 / 4 : ℝ) = 1 := tendsto_nhds_unique h2 h1
  norm_num at hval

/-- **DERIVED (Task 35), PRINCIPAL — weak solder data are strictly weaker than regular ones.**
There is a weak Task-34 solder datum on a Task-33 emergent smooth manifold which is induced
by **no** regular solder datum: its local representative in the actual tangent
trivialization is discontinuous, whereas the representative of any regular datum is
continuous (indeed `C^∞`).

`TangentSolderData` therefore does **not** imply `SmoothTangentSolderData`, and the Task-34
gate really did leave the regularity gap open. -/
theorem weak_solder_not_regular :
    ∃ E : TangentSolderData flatBase
        (trivialCocycle (↥SpinGroup) (emergentCover flatBase)),
      ∀ E' : SmoothTangentSolderData flatBase
        (trivialCocycle (↥SpinGroup) (emergentCover flatBase)),
        (E'.toTangentSolderData flatBase_smoothGluing).frame ≠ E.frame := by
  refine ⟨badSolder, fun E' hframe => ?_⟩
  have hcont := E'.continuousOn_weakTangentRep flatBase_smoothGluing ()
    ⟨⟨0, Set.mem_univ 0⟩⟩ sOne
  have heq : ∀ x : Space flatBase,
      weakTangentRep (E'.toTangentSolderData flatBase_smoothGluing) () x sOne
        = weakTangentRep badSolder () x sOne := by
    intro x
    show flatBase.tangentTransitionMap (flatBase.outIndex x) () (flatBase.outCoord x)
        ((E'.toTangentSolderData flatBase_smoothGluing).frame () x sOne) = _
    rw [hframe]
    rfl
  refine badSolder_rep_not_continuousOn ?_
  have : ContinuousOn (fun x => (weakTangentRep
      (E'.toTangentSolderData flatBase_smoothGluing) () x sOne).1)
      (flatBase.chartRange ()) := continuous_fst.comp_continuousOn hcont
  exact this.congr fun x _ => congrArg Prod.fst (heq x).symm

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.SmoothTangentSolderData.weakTangentRep_eq
#print axioms SpinNative.badSolder
#print axioms SpinNative.badSolder_rep_not_continuousOn
#print axioms SpinNative.badSolder_metric_not_continuousOn
#print axioms SpinNative.weak_solder_not_regular
