import RequestProject.Spine.Task36.OrientationGate
import RequestProject.Spine.Task36.TimeOrientation
import RequestProject.Spine.Solder.RegularExamples
import RequestProject.Spine.SpinNative.KernelTwist

/-!
# Task 36 / Adversarial : the trivial positive control — no nontrivial gluing (§6)

**Seventh module of the Task-36 battery.**

The baseline against which every later gluing test is compared: a base with **one chart**, no
nontrivial incidence, trivial tangent transition and trivial native Spin transition.  It is
the symmetric Task-33 gluing over the one-element index type with the whole local model as its
domain.

What is proved, at the exact project-native level:

* `Task36.oneChart_no_overlap_obstruction` — every kernel-valued Čech 1-cocycle on the cover is
  *pointwise* trivial, and every native Spin transition datum is pointwise the unit on the
  overlaps.  So on this base there is **no residual family of global sign choices at all** —
  the sign freedom exhibited by the loop controls is genuinely produced by the gluing, not by
  the local model;
* `Task36.oneChart_positive_control` — the regular solder exists, the orientation
  compatibility of the atlas holds (as a consequence of the solder, via the orientation gate),
  and a time-orientation reduction exists and is glued.

## Non-claim (§6, last sentence)

Nothing here infers *uniqueness of the Spin structure* from contractibility: what is proved is
the exact fixed-cover statement that on a one-patch cover the kernel cocycles are pointwise
trivial.  No classification theorem for Spin structures is available in the project, and none
is used.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

/-! ## Subsingleton covers carry no kernel freedom -/

section Subsingleton

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  [Subsingleton ι] {𝓤 : CechCover X ι}

/-- **DERIVED (Task 36).**  On a cover with one patch every kernel-valued Čech 1-cocycle is
pointwise trivial: there is no sign freedom whatsoever. -/
theorem kerCocycle_pointwiseTrivial_of_subsingleton {P : InternalProjection L G}
    (ε : KerCocycle P 𝓤) : ε.IsPointwiseTrivial := by
  intro i j x hx
  have hij : i = j := Subsingleton.elim i j
  subst hij
  exact ε.e_self i hx.1

omit [IsTopologicalGroup L] in
/-- **DERIVED (Task 36).**  On a cover with one patch every transition datum is pointwise the
unit on the overlaps: the lift carries no information. -/
theorem cocycle_trivial_of_subsingleton (S : VisibleCocycle L 𝓤) (i j : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₂ i j) : S.g i j x = 1 := by
  have hij : i = j := Subsingleton.elim i j
  subst hij
  exact S.g_self i hx.1

end Subsingleton

/-! ## The one-chart base -/

/-- **NEWLY DEFINED (Task 36).**  The one-chart base: the symmetric Task-33 gluing over the
one-element index type, with the whole local model as its single domain.  Its emergent base is
a single chart image, its identification maps are the identity, and its tangent transitions
are the identity. -/
def oneChartGluing : BaseGluingData LocalModel Unit :=
  symmetricGluing Unit (isOpen_univ : IsOpen (Set.univ : Set LocalModel))

theorem oneChartGluing_smoothGluing : oneChartGluing.SmoothGluing :=
  symmetricGluing.smoothGluing _

theorem oneChartGluing_isManifold :
    IsManifold localModelI (⊤ : ℕ∞) (Space oneChartGluing) :=
  isManifold_of_smoothGluing oneChartGluing_smoothGluing

/-- The trivial native Spin seed on the one-chart base. -/
def oneChartSpin : NativeSpinTransitionData ↥SpinGroup (emergentCover oneChartGluing) :=
  trivialCocycle (↥SpinGroup) (emergentCover oneChartGluing)

/-- **NEWLY DEFINED (Task 36).**  The regular solder of the one-chart base: the constant
identity comparison. -/
def oneChartSolder : SmoothTangentSolderData oneChartGluing oneChartSpin :=
  symmetricRegularSolder Unit (isOpen_univ : IsOpen (Set.univ : Set LocalModel))

/-- **DERIVED (Task 36), §6 — no overlap obstruction and no artificial sign family.** -/
theorem oneChart_no_overlap_obstruction :
    (∀ ε : KerCocycle internalSpinProjection (emergentCover oneChartGluing),
      ε.IsPointwiseTrivial) ∧
    (∀ (S : NativeSpinTransitionData ↥SpinGroup (emergentCover oneChartGluing)) (i j : Unit),
      ∀ x ∈ (emergentCover oneChartGluing).overlap₂ i j, S.g i j x = 1) :=
  ⟨fun ε => kerCocycle_pointwiseTrivial_of_subsingleton ε,
   fun S i j _ hx => cocycle_trivial_of_subsingleton S i j hx⟩

/-- **DERIVED (Task 36), PRINCIPAL §6 — the trivial positive control.**

On the one-chart base:

1. the gluing is smooth and the emergent base is a `C^∞` four-manifold;
2. the native Spin lift is pointwise trivial on the overlaps;
3. a regular solder exists;
4. orientation compatibility of the atlas holds — as a *consequence* of 3, through the
   orientation gate, not as an assumption;
5. a time-orientation (future-cone) reduction exists, and its distinguished representative
   glues;
6. there is no residual family of global sign choices: every kernel 1-cocycle is pointwise
   trivial. -/
theorem oneChart_positive_control :
    oneChartGluing.SmoothGluing ∧
    IsManifold localModelI (⊤ : ℕ∞) (Space oneChartGluing) ∧
    (∀ (i j : Unit) (x : Space oneChartGluing), oneChartSpin.g i j x = 1) ∧
    Nonempty (SmoothTangentSolderData oneChartGluing oneChartSpin) ∧
    (∃ a : Unit → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) (oneChartGluing.D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ oneChartGluing.W i j,
        LinearMap.det ((oneChartGluing.tangentTransitionMap i j y :
            LocalModel →ₗ[ℝ] LocalModel)) * a i y = a j (oneChartGluing.φ i j y))) ∧
    (∃ R : TimeOrientationReduction oneChartGluing, R.IsGlued) ∧
    (∀ ε : KerCocycle internalSpinProjection (emergentCover oneChartGluing),
      ε.IsPointwiseTrivial) := by
  refine ⟨oneChartGluing_smoothGluing, oneChartGluing_isManifold, fun _ _ _ => rfl,
    ⟨oneChartSolder⟩, smooth_solder_implies_orientation_compatible oneChartSolder,
    ⟨solder_timeOrientationReduction oneChartSolder, ?_⟩,
    fun ε => kerCocycle_pointwiseTrivial_of_subsingleton ε⟩
  intro i j y hy
  exact oneChartSolder.timeField_glue_of_trivial
    (fun a b x => projectedLorentzTransition_trivial a b x) i j hy

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.kerCocycle_pointwiseTrivial_of_subsingleton
#print axioms Task36.oneChartSolder
#print axioms Task36.oneChart_no_overlap_obstruction
#print axioms Task36.oneChart_positive_control
