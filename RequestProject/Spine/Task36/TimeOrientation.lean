import RequestProject.Spine.Solder.OrientationTime

/-!
# Task 36 / Repair C : time-orientation *reduction* versus the distinguished time field (§3)

**Sixth module of the Task-36 battery — a Task-35 closure repair.**

Task 35 proved `SpinNative.SmoothTangentSolderData.timeField_glue_iff`: the *distinguished*
local field `A_i(𝟙_𝒮)` glues along the genuine tangent transitions exactly when the projected
internal Lorentz transition fixes the intrinsic unit `𝟙_𝒮`.

**That theorem is not an obstruction to time orientability, and must not be read as one.**
It is a statement about one particular local representative — the image of a *fixed* internal
vector — and the projected Lorentz transitions of course move that vector in general, which is
merely a statement about the chosen representative, not about the cone field.

This module makes the distinction structural.

* `Task36.TimeOrientationReduction` packages what a regular solder actually forces: a field of
  future cones in chart coordinates which is carried onto itself by the genuine tangent
  transitions of the Task-33 atlas, together with a `C^∞` future-directed local representative
  on every chart domain.
* `Task36.solder_timeOrientationReduction` — **a regular solder always produces one**.  So

      regular solder  →  coherent smooth future-cone (time-orientation) reduction on TM

  is a theorem, with no extra hypothesis whatsoever.
* the *loop-specific* positive control — on the periodic fixed-cover loop model with a
  kernel-twisted Spin seed the local representatives even glue — is **not** part of this
  module.  Task 37 moved it to the adversarial control module
  `RequestProject.Spine.Task36.LoopTimeOrientation`, so that the general layer no longer
  depends on any loop model (`Task36.loop_timeOrientationReduction_isGlued` is unchanged as a
  statement).

## Classification (the honest §3 answer)

```text
time-orientation (future-cone) reduction            : DERIVED   (this module)
C^∞ future-directed local representative per chart  : DERIVED   (Task 35)
gluing of the *distinguished* representative        : iff the projected Lorentz cocycle
                                                      fixes 𝟙_𝒮 (Task 35) — a statement
                                                      about that representative only
global smooth future-directed timelike section of TM: ADDITIONAL THEOREM /
                                                      INFRASTRUCTURE BLOCKER
```

The exact missing ingredients for the last line, in this project at this stage, are:

1. the emergent base is Hausdorff only under `BaseGluingData.ClosedGluingGraph` and second
   countable only for a countable index type, so `ParacompactSpace (Space B)` — the hypothesis
   of every partition-of-unity result in the pinned Mathlib — is not available in general;
2. the project has no total-space presentation of `TM` as a smooth vector bundle with a
   `C^∞`-section API (Task 35 records this as the packaging blocker), so a partition-of-unity
   sum of the local representatives cannot even be *written* as a section;
3. no convexity lemma for the intrinsic interior future `SpinCore.IntFuture` is available, and
   convexity of the cone is what makes such a sum future-directed.

None of these is a mathematical obstruction; all three are missing infrastructure, and they are
recorded as such in `TASK36_AUDIT.md` §3.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

universe t

/-- **NEWLY DEFINED (Task 36), §3 — the time-orientation reduction.**

A coherent field of future cones on the emergent manifold, in chart coordinates: a cone in
each tangent chart, carried onto the cone of the other chart by the *genuine* tangent
transition of the Task-33 atlas, together with a `C^∞` representative inside it on each chart
domain.

This is the structure that a regular solder forces.  It is deliberately *not* a global section:
a section is `Task36.TimeOrientationReduction.rep` glued, and gluing is a separate question. -/
structure TimeOrientationReduction {ι : Type t} (B : BaseGluingData LocalModel ι) where
  /-- The future cone in the chart components of the piece `i` at the coordinate `y`. -/
  cone : ι → LocalModel → Set LocalModel
  /-- The cones are carried onto each other by the genuine tangent transitions. -/
  transform : ∀ (i j : ι), ∀ y ∈ B.W i j, ∀ u : LocalModel,
    u ∈ cone i y ↔ B.tangentTransitionMap i j y u ∈ cone j (B.φ i j y)
  /-- A distinguished local representative. -/
  rep : ι → LocalModel → LocalModel
  /-- It is smooth on the chart domain. -/
  contDiffOn_rep : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (rep i) (B.D i)
  /-- It lies in the cone at every point, so every cone is nonempty. -/
  rep_mem : ∀ i y, rep i y ∈ cone i y

namespace TimeOrientationReduction

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

theorem cone_nonempty (R : TimeOrientationReduction B) (i : ι) (y : LocalModel) :
    (R.cone i y).Nonempty :=
  ⟨R.rep i y, R.rep_mem i y⟩

/-- The reduction is *global* when the distinguished representatives glue along the genuine
tangent transitions; then they define one field on the emergent manifold. -/
def IsGlued (R : TimeOrientationReduction B) : Prop :=
  ∀ (i j : ι), ∀ y ∈ B.W i j,
    B.tangentTransitionMap i j y (R.rep i y) = R.rep j (B.φ i j y)

end TimeOrientationReduction

/-- **NEWLY DEFINED (Task 36), PRINCIPAL (§3) — the regular solder gives a time-orientation
reduction.**

No hypothesis beyond the existence of the regular solder: the cone field is the solder
pull-back of the intrinsic interior future, the transformation law is orthochronicity of the
projected native Lorentz transitions, and the representative is the Task-35 local time
field. -/
def solder_timeOrientationReduction {ι : Type t} {B : BaseGluingData LocalModel ι}
    {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
    (E : SmoothTangentSolderData B S) : TimeOrientationReduction B where
  cone := E.futureCone
  transform i j _ hy u := E.futureCone_transform i j hy u
  rep := E.timeField
  contDiffOn_rep := E.contDiffOn_timeField
  rep_mem := E.timeField_mem_futureCone

/-- **DERIVED (Task 36), §3.**  A regular solder always yields a coherent smooth future-cone
reduction; this is the exact sense in which "regular solder → time orientation" is a theorem
of the project. -/
theorem nonempty_timeOrientationReduction_of_solder {ι : Type t}
    {B : BaseGluingData LocalModel ι}
    {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
    (E : SmoothTangentSolderData B S) : Nonempty (TimeOrientationReduction B) :=
  ⟨solder_timeOrientationReduction E⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.TimeOrientationReduction
#print axioms Task36.solder_timeOrientationReduction
#print axioms Task36.nonempty_timeOrientationReduction_of_solder
