import RequestProject.Spine.Solder.RegularGauge

/-!
# Task 36 / §4 : the regular tangent gauge as a group acting on regular solder data

**Task-35 cleanup module.**

Task 35 proved the two substantive facts about the residual freedom of a regular solder
(`SpinNative.SmoothTangentSolderData.exists_regularGauge`, transitivity, and
`SpinNative.SmoothTangentSolderData.regularGauge_unique`, freeness) but did **not** package
`SpinNative.RegularTangentGauge B` as a group, so the word "torsor" was carried by wording
rather than by a formal action.  Task 36 §4 closes that gap, **without touching the frozen
Task-35 statements**: everything here is new and lives in the adversarial layer.

## What is added

* `Task36.RegularTangentGauge.gauge_ext` — a gauge field is determined by its local
  representatives (all other fields are propositions);
* `one`, `mul`, `inv` for `SpinNative.RegularTangentGauge B` and the `Group` instance;
* the `MulAction` instance on `SpinNative.SmoothTangentSolderData B S`, with
  `Task36.act_one` and `Task36.act_mul` as the defining laws;
* `Task36.regularGauge_isPretransitive` — the action is pretransitive (Task-35 transitivity);
* `Task36.regularGauge_free` — the action is free (Task-35 freeness), hence the action is
  also faithful whenever a regular solder exists;
* `Task36.regular_solder_is_gauge_torsor` — the packaged statement: for a *nonempty* set of
  regular solder data the action of the regular tangent gauge group is free and transitive.

## Naming discipline (§17)

Mathlib's `AddTorsor` is additive; there is no multiplicative torsor class in the pinned
Mathlib, so the strongest standard packaging available is

```text
    Group G, MulAction G X, MulAction.IsPretransitive G X, plus a freeness theorem
```

which is exactly what is proved here.  Statements elsewhere in the project should say
"**free and transitive regular gauge action**" rather than naming a Mathlib torsor structure.

Smoothness of the inverse gauge field is *not* an extra datum: it is derived exactly as
`SpinNative.SmoothTangentSolderData.contDiffOn_A_symm` is, from
`contDiffAt_map_inverse`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}
  {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

/-! ## Extensionality -/

/-- **NEWLY DEFINED (Task 36), §4.**  A regular tangent gauge field is determined by its
local representatives; the remaining fields are propositions. -/
theorem gauge_ext {g g' : RegularTangentGauge B} (h : g.a = g'.a) : g = g' := by
  cases g; cases g'; cases h; rfl

/-- **NEWLY DEFINED (Task 36), §4.**  A regular solder datum is determined by its local
comparison field. -/
theorem solder_ext {E E' : SmoothTangentSolderData B S} (h : E.A = E'.A) : E = E' := by
  cases E; cases E'; cases h; rfl

/-! ## The group structure -/

/-- **NEWLY DEFINED (Task 36), §4.**  The identity gauge field. -/
def gaugeOne (B : BaseGluingData LocalModel ι) : RegularTangentGauge B where
  a _ _ := ContinuousLinearEquiv.refl ℝ LocalModel
  contDiffOn_a _ := contDiffOn_const
  compat _ _ _ _ _ := rfl

/-- **NEWLY DEFINED (Task 36), §4.**  Composition of gauge fields: `gaugeMul g h` acts as
`g` after `h`. -/
def gaugeMul (g h : RegularTangentGauge B) : RegularTangentGauge B where
  a i y := (h.a i y).trans (g.a i y)
  contDiffOn_a i := (g.contDiffOn_a i).clm_comp (h.contDiffOn_a i)
  compat i j y hy v := by
    show g.a j (B.φ i j y) (h.a j (B.φ i j y) (B.tangentTransitionMap i j y v))
      = B.tangentTransitionMap i j y (g.a i y (h.a i y v))
    rw [h.compat i j y hy v, g.compat i j y hy (h.a i y v)]

/-- **DERIVED (Task 36), §4.**  The pointwise inverse of a gauge field is again smooth; the
argument is the one used for `SpinNative.SmoothTangentSolderData.contDiffOn_A_symm`. -/
theorem contDiffOn_gauge_symm (g : RegularTangentGauge B) (i : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (((g.a i y).symm : LocalModel →L[ℝ] LocalModel))) (B.D i) := by
  intro y hy
  have ha : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => ((g.a i y : LocalModel →L[ℝ] LocalModel))) y :=
    (g.contDiffOn_a i).contDiffAt ((B.isOpen_D i).mem_nhds hy)
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (ContinuousLinearMap.inverse : (LocalModel →L[ℝ] LocalModel) →
        (LocalModel →L[ℝ] LocalModel)) ((g.a i y : LocalModel →L[ℝ] LocalModel)) :=
    contDiffAt_map_inverse (g.a i y)
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z => ContinuousLinearMap.inverse ((g.a i z : LocalModel →L[ℝ] LocalModel))) y :=
    ContDiffAt.comp (g := ContinuousLinearMap.inverse)
      (f := fun z => ((g.a i z : LocalModel →L[ℝ] LocalModel))) y hinv ha
  refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards with z
  exact (ContinuousLinearMap.inverse_equiv (g.a i z)).symm

/-- **NEWLY DEFINED (Task 36), §4.**  The inverse gauge field. -/
def gaugeInv (g : RegularTangentGauge B) : RegularTangentGauge B where
  a i y := (g.a i y).symm
  contDiffOn_a i := contDiffOn_gauge_symm g i
  compat i j y hy v := by
    show (g.a j (B.φ i j y)).symm (B.tangentTransitionMap i j y v)
      = B.tangentTransitionMap i j y ((g.a i y).symm v)
    have h := g.compat i j y hy ((g.a i y).symm v)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [← h, ContinuousLinearEquiv.symm_apply_apply]

instance : One (RegularTangentGauge B) := ⟨gaugeOne B⟩
instance : Mul (RegularTangentGauge B) := ⟨gaugeMul⟩
instance : Inv (RegularTangentGauge B) := ⟨gaugeInv⟩

@[simp] theorem gauge_one_a (i : ι) (y v : LocalModel) :
    (1 : RegularTangentGauge B).a i y v = v := rfl

@[simp] theorem gauge_mul_a (g h : RegularTangentGauge B) (i : ι) (y v : LocalModel) :
    (g * h).a i y v = g.a i y (h.a i y v) := rfl

@[simp] theorem gauge_inv_a (g : RegularTangentGauge B) (i : ι) (y v : LocalModel) :
    (g⁻¹).a i y v = (g.a i y).symm v := rfl

/-- **DERIVED (Task 36), §4 — the group laws.** -/
instance : Group (RegularTangentGauge B) where
  mul_assoc g h k := by
    refine gauge_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
    exact funext fun v => rfl
  one_mul g := by
    refine gauge_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
    exact funext fun v => rfl
  mul_one g := by
    refine gauge_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
    exact funext fun v => rfl
  inv_mul_cancel g := by
    refine gauge_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
    exact funext fun v => (g.a i y).symm_apply_apply v

/-! ## The action on regular solder data -/

instance : SMul (RegularTangentGauge B) (SmoothTangentSolderData B S) :=
  ⟨fun g E => g.act E⟩

@[simp] theorem smul_A (g : RegularTangentGauge B) (E : SmoothTangentSolderData B S)
    (i : ι) (y v : LocalModel) : (g • E).A i y v = g.a i y (E.A i y v) := rfl

/-- **DERIVED (Task 36), §4 — `act_one`.** -/
theorem act_one (E : SmoothTangentSolderData B S) : (1 : RegularTangentGauge B) • E = E := by
  refine solder_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
  exact funext fun v => rfl

/-- **DERIVED (Task 36), §4 — `act_mul`.** -/
theorem act_mul (g h : RegularTangentGauge B) (E : SmoothTangentSolderData B S) :
    (g * h) • E = g • (h • E) := by
  refine solder_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
  exact funext fun v => rfl

/-- **DERIVED (Task 36), §4 — preservation of regular solder data, packaged as an action.**
The gauge group acts on the regular solder data of the *same* emergent base and the *same*
native Spin seed: the regularity and the exact intertwining law are both preserved. -/
instance : MulAction (RegularTangentGauge B) (SmoothTangentSolderData B S) where
  one_smul := act_one
  mul_smul := act_mul

/-! ## Freeness and transitivity -/

/-- **DERIVED (Task 36), §4 — transitivity of the action.**  This is the Task-35 theorem
`SpinNative.SmoothTangentSolderData.exists_regularGauge`, now as a Mathlib
`MulAction.IsPretransitive` instance. -/
instance regularGauge_isPretransitive :
    MulAction.IsPretransitive (RegularTangentGauge B) (SmoothTangentSolderData B S) where
  exists_smul_eq E E' := by
    obtain ⟨g, hg⟩ := E.exists_regularGauge E'
    refine ⟨g, solder_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)⟩
    exact funext fun v => hg i y v

/-- **DERIVED (Task 36), §4 — freeness of the action.**  This is the Task-35 theorem
`SpinNative.SmoothTangentSolderData.regularGauge_unique`, stated for the action. -/
theorem regularGauge_free (E : SmoothTangentSolderData B S)
    {g g' : RegularTangentGauge B} (h : g • E = g' • E) : g = g' := by
  refine gauge_ext (funext fun i => funext fun y => ContinuousLinearEquiv.ext ?_)
  refine funext fun w => E.regularGauge_unique g g' (fun i y v => ?_) i y w
  rw [show (g.act E) = g • E from rfl, show (g'.act E) = g' • E from rfl, h]

/-- **DERIVED (Task 36), §4 — faithfulness.**  The action is faithful once one
regular solder exists. -/
theorem regularGauge_faithful (E : SmoothTangentSolderData B S)
    {g g' : RegularTangentGauge B}
    (h : ∀ F : SmoothTangentSolderData B S, g • F = g' • F) : g = g' :=
  regularGauge_free E (h E)

/-- **DERIVED (Task 36), PRINCIPAL §4 — the free and transitive regular gauge action.**

For a fixed emergent base and a fixed native Spin seed, the regular tangent gauge fields form
a group acting on the regular solder data, and the action is free and transitive.  This is the
exact content of the word "torsor" as used in the Task-35 documentation; the pinned Mathlib
has no multiplicative torsor class, so the packaging is `Group` + `MulAction` +
`MulAction.IsPretransitive` + freeness. -/
theorem regular_solder_is_gauge_torsor (E : SmoothTangentSolderData B S) :
    (∀ (g : RegularTangentGauge B) (i : ι) (y v : LocalModel),
        (g • E).A i y v = g.a i y (E.A i y v)) ∧
    (∀ E' : SmoothTangentSolderData B S, ∃ g : RegularTangentGauge B, g • E = E') ∧
    (∀ g g' : RegularTangentGauge B, g • E = g' • E → g = g') :=
  ⟨fun _ _ _ _ => rfl,
   fun E' => MulAction.exists_smul_eq (RegularTangentGauge B) E E',
   fun _ _ h => regularGauge_free E h⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.gauge_ext
#print axioms Task36.solder_ext
#print axioms Task36.act_one
#print axioms Task36.act_mul
#print axioms Task36.regularGauge_isPretransitive
#print axioms Task36.regularGauge_free
#print axioms Task36.regular_solder_is_gauge_torsor
