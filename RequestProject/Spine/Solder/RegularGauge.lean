import RequestProject.Spine.Solder.OrientationTime

/-!
# Spine / Solder : the residual gauge freedom of a *regular* solder

**Seventh module of the Task-35 regularity layer (Task 35 §11).**

Task 34 called the compatible weak solder data "a torsor under the pointwise automorphism
fields of `TM`".  The group there was the group of *arbitrary* pointwise automorphism
fields — a group far too large to be the automorphism group of the tangent bundle, and the
word "torsor" was used without a freeness/transitivity theorem in that formulation.  Task 35
repairs both points for the regular structure.

## The correct gauge group

`SpinNative.RegularTangentGauge B` — a **regular (smooth) automorphism field of the tangent
bundle**, in the local representatives of the actual Task-33 atlas:

* `a i : LocalModel → (LocalModel ≃L[ℝ] LocalModel)`, `C^∞` on `D i`;
* the tangent-compatibility law `a j (φ_ij y) ∘ D(φ_ij)(y) = D(φ_ij)(y) ∘ a i y`, which says
  exactly that the local representatives are the chart expressions of *one* automorphism of
  the tangent bundle, not of an unrelated family.

## The theorems

* `SpinNative.RegularTangentGauge.act` — the action on regular solder data: it preserves the
  structure (regularity and the exact intertwining law are both stable);
* `SpinNative.SmoothTangentSolderData.exists_regularGauge` — **transitivity**: any two
  regular solder data for the same `(B, S)` differ by one regular gauge field;
* `SpinNative.SmoothTangentSolderData.regularGauge_unique` — **freeness**: the gauge field
  relating them is unique.

Transitivity and freeness together are what justifies the word *torsor*, and they are now
theorems rather than wording: the regular solder data for a fixed emergent base and a fixed
Spin seed form a torsor under the group of regular tangent-bundle automorphism fields.  (The
group structure itself is not packaged as a Mathlib `Group` instance; the two theorems above
are the exact content.)

## UPDATE NOTICE (Task 36 §4) — the action is now packaged

The parenthesis above is superseded.  `RequestProject.Spine.Task36.GaugeGroup` supplies, with
no change to any statement of this module:

* `Group (SpinNative.RegularTangentGauge B)` — identity, composition, inverse and the group
  laws (smoothness of the inverse field is *derived*, `Task36.contDiffOn_gauge_symm`);
* `MulAction (SpinNative.RegularTangentGauge B) (SpinNative.SmoothTangentSolderData B S)` —
  with `Task36.act_one` and `Task36.act_mul`, so preservation of regular solder data is part
  of the action;
* `Task36.regularGauge_isPretransitive` (transitivity) and `Task36.regularGauge_free`
  (freeness), bundled as `Task36.regular_solder_is_gauge_torsor`.

The pinned Mathlib has no *multiplicative* torsor class (`AddTorsor` is additive), so the
strongest standard packaging available is `Group` + `MulAction` + `MulAction.IsPretransitive`
+ freeness.  Documentation should accordingly say "**free and transitive regular gauge
action**" rather than naming a Mathlib torsor structure.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **NEWLY DEFINED (Task 35).**  A regular (smooth) automorphism field of the tangent bundle
of the Task-33 emergent manifold, given by its local representatives in the actual atlas: a
`C^∞` family of automorphisms of the local model for each chart, intertwined by the genuine
tangent transitions `D(φ_ij)`. -/
structure RegularTangentGauge (B : BaseGluingData LocalModel ι) where
  /-- The local representatives. -/
  a : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel)
  /-- Regularity. -/
  contDiffOn_a : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun y => ((a i y : LocalModel →L[ℝ] LocalModel))) (B.D i)
  /-- The representatives are the chart expressions of one tangent-bundle automorphism. -/
  compat : ∀ (i j : ι), ∀ y ∈ B.W i j, ∀ v : LocalModel,
    a j (B.φ i j y) (B.tangentTransitionMap i j y v)
      = B.tangentTransitionMap i j y (a i y v)

namespace RegularTangentGauge

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

/-- **NEWLY DEFINED (Task 35).**  The action of a regular gauge field on a regular solder
datum.  The intertwining law is preserved: the gauge acts on the *tangent* side, the Lorentz
transition on the *internal* side, and the two commute by the compatibility law. -/
def act (g : RegularTangentGauge B) (E : SmoothTangentSolderData B S) :
    SmoothTangentSolderData B S where
  A i y := (E.A i y).trans (g.a i y)
  contDiffOn_A i := (g.contDiffOn_a i).clm_comp (E.contDiffOn_A i)
  intertwine i j y hy v := by
    show g.a j (B.φ i j y) (E.A j (B.φ i j y) v)
      = B.tangentTransitionMap i j y (g.a i y (E.A i y
          (projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v)))
    rw [E.intertwine i j y hy v, g.compat i j y hy]

@[simp] theorem act_A (g : RegularTangentGauge B) (E : SmoothTangentSolderData B S)
    (i : ι) (y v : LocalModel) : (g.act E).A i y v = g.a i y (E.A i y v) := rfl

end RegularTangentGauge

namespace SmoothTangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

/-- **DERIVED (Task 35), transitivity.**  Any two regular solder data for the same emergent
base and the same Spin seed differ by exactly one regular gauge field: the pointwise
comparison `A' i y ∘ (A i y)⁻¹` is smooth and satisfies the tangent-compatibility law. -/
theorem exists_regularGauge (E E' : SmoothTangentSolderData B S) :
    ∃ g : RegularTangentGauge B, ∀ i y v, (g.act E).A i y v = E'.A i y v := by
  refine ⟨{ a := fun i y => (E.A i y).symm.trans (E'.A i y)
            contDiffOn_a := fun i => (E'.contDiffOn_A i).clm_comp (E.contDiffOn_A_symm i)
            compat := fun i j y hy v => ?_ }, fun i y v => ?_⟩
  · -- the comparison is intertwined by the genuine tangent transitions
    show E'.A j (B.φ i j y) ((E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y v))
      = B.tangentTransitionMap i j y (E'.A i y ((E.A i y).symm v))
    rw [E.frameChange_symm i j hy v]
    have hsymm := projectedLorentzTransition_symm S j i
      (x := B.chart i ⟨y, B.W_subset i j hy⟩)
      ⟨by rw [B.chart_eq_chart_of_mem_W i j hy]; exact ⟨_, rfl⟩, ⟨_, rfl⟩⟩
      ((E.A i y).symm v)
    have hlaw := E'.intertwine i j y hy
      (projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩)
        ((E.A i y).symm v))
    rw [hsymm] at hlaw
    exact hlaw
  · show (E.A i y).symm.trans (E'.A i y) (E.A i y v) = E'.A i y v
    show E'.A i y ((E.A i y).symm (E.A i y v)) = E'.A i y v
    rw [ContinuousLinearEquiv.symm_apply_apply]

/-- **DERIVED (Task 35), freeness.**  The regular gauge field relating two regular solder
data is unique; in particular a gauge field acting trivially on one regular solder datum is
the identity. -/
theorem regularGauge_unique (E : SmoothTangentSolderData B S)
    (g g' : RegularTangentGauge B)
    (hact : ∀ i y v, (g.act E).A i y v = (g'.act E).A i y v) (i : ι) (y w : LocalModel) :
    g.a i y w = g'.a i y w := by
  have h := hact i y ((E.A i y).symm w)
  show g.a i y w = g'.a i y w
  rw [RegularTangentGauge.act_A, RegularTangentGauge.act_A,
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

/-- **DERIVED (Task 35), PACKAGED — the exact residual freedom of a regular solder.**  The
regular solder data for a fixed emergent base and a fixed Spin seed form a torsor under the
regular (smooth) tangent-bundle automorphism fields: the action preserves the structure, it
is transitive, and it is free.  No solder field is canonical, and the gauge group is the
*correct* one — not the group of arbitrary pointwise automorphism fields of Task 34. -/
theorem regular_solder_torsor (E : SmoothTangentSolderData B S) :
    (∀ g : RegularTangentGauge B, ∀ i y v, (g.act E).A i y v = g.a i y (E.A i y v)) ∧
    (∀ E' : SmoothTangentSolderData B S,
      ∃ g : RegularTangentGauge B, ∀ i y v, (g.act E).A i y v = E'.A i y v) ∧
    (∀ g g' : RegularTangentGauge B,
      (∀ i y v, (g.act E).A i y v = (g'.act E).A i y v) →
        ∀ i y w, g.a i y w = g'.a i y w) :=
  ⟨fun _ _ _ _ => rfl,
   fun E' => E.exists_regularGauge E',
   fun g g' hact i y w => E.regularGauge_unique g g' hact i y w⟩

end SmoothTangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.RegularTangentGauge
#print axioms SpinNative.RegularTangentGauge.act
#print axioms SpinNative.SmoothTangentSolderData.exists_regularGauge
#print axioms SpinNative.SmoothTangentSolderData.regularGauge_unique
#print axioms SpinNative.SmoothTangentSolderData.regular_solder_torsor
