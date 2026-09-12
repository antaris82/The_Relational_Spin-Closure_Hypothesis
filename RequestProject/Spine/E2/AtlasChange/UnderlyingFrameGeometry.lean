import RequestProject.Spine.E2.Defect.FrameFamilyRealization

/-!
# Task 32, Package A: the bare underlying frame geometry, separated from atlas data

**HARD TARGET A, first step (items 13–15).**

The inherited Task-XXVII object `TopologicalFrameFamily` packages *two* logically distinct
things:

* the **bare metric-oriented rank-three family** `family : MetricOrientedRankThreeFamily B E`
  — the geometry itself;
* an **ordinary atlas presentation** `atlas : MetricOrientedFibreAtlas family ι` — a choice of
  open cover together with metric- and orientation-preserving local trivializations.

Task XXXI worked throughout with a *fixed* presentation.  This module introduces the neutral
projection/interface separating the two layers, **without changing the frozen Task-XXVII
definition** (item 15):

* `BareMetricOrientedFamily` / `UnderlyingFrameGeometry` — neutral names for the bare object;
* `TopologicalFrameFamily.underlying` — the projection onto it;
* `OrdinaryAtlasPresentation` — a neutral name for the presentation datum;
* `ordinarySystem` — the ordinary transition system produced by a presentation alone, proved
  equal to the inherited `TopologicalFrameFamily.toOrdinaryTransitionSystem`;
* `presentedFamily` — the reassembly, with `underlying_presentedFamily` proving that the bare
  layer is exactly what it was.

Nothing here is a mathematical theorem about liftability; it is the interface that makes the
question *"does the Task-XXXI defect depend on the presentation?"* expressible at all.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask31

universe u v t

section Bare

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **PACKAGE A (item 13), principal definition.**  The *bare metric-oriented rank-three
family*: the inherited Task-XXVI geometric datum with **no** atlas, no cover and no choice of
local trivialization.  This is a neutral re-exposure, not a redefinition (firewall item 3). -/
abbrev BareMetricOrientedFamily (B : Type u) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] : Type _ :=
  MetricOrientedRankThreeFamily B E

/-- **PACKAGE A (item 13).**  Second suggested neutral name for the same object. -/
abbrev UnderlyingFrameGeometry (B : Type u) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] : Type _ :=
  BareMetricOrientedFamily B E

/-- **PACKAGE A (item 14), principal definition.**  An *ordinary atlas presentation* of a bare
family: exactly the Task-XXVII datum recovering an open cover, metric/orientation-preserving
local trivializations and hence ordinary transition maps. -/
abbrev OrdinaryAtlasPresentation (F : BareMetricOrientedFamily B E) (ι : Type t) : Type _ :=
  MetricOrientedFibreAtlas F ι

variable {ι : Type t}

/-- **PACKAGE A (item 13), the projection.**  The bare family underlying an inherited
topological frame family. -/
def bareOf (T : TopologicalFrameFamily B E ι) : BareMetricOrientedFamily B E :=
  T.family

/-- **PACKAGE A (item 14), the presentation.** -/
def presentationOf (T : TopologicalFrameFamily B E ι) :
    OrdinaryAtlasPresentation (bareOf T) ι :=
  T.atlas

/-- **PACKAGE A.**  Reassembly of a bare family and a presentation of it. -/
def presentedFamily (F : BareMetricOrientedFamily B E) (A : OrdinaryAtlasPresentation F ι) :
    TopologicalFrameFamily B E ι :=
  ⟨F, A⟩

@[simp] theorem bareOf_presentedFamily (F : BareMetricOrientedFamily B E)
    (A : OrdinaryAtlasPresentation F ι) : bareOf (presentedFamily F A) = F := rfl

@[simp] theorem presentationOf_presentedFamily (F : BareMetricOrientedFamily B E)
    (A : OrdinaryAtlasPresentation F ι) : presentationOf (presentedFamily F A) = A := rfl

/-- **PACKAGE A.**  Every inherited frame family is the reassembly of its own bare layer and
its own presentation: the separation loses nothing. -/
theorem presentedFamily_bareOf_presentationOf (T : TopologicalFrameFamily B E ι) :
    presentedFamily (bareOf T) (presentationOf T) = T := rfl

/-! ## The ordinary transition system of a presentation alone -/

/-- **PACKAGE A (item 14), principal definition.**  The ordinary transition system determined
by a presentation of a bare family.  Every field is the inherited Task-XXVII one. -/
noncomputable def ordinarySystem {F : BareMetricOrientedFamily B E}
    (A : OrdinaryAtlasPresentation F ι) : NullSectorTask27.OrdinaryTransitionSystem B ι where
  U := A.U
  isOpen_U := A.isOpen_U
  cover := A.cover
  g := A.transitionFun
  continuous_g := A.continuous_transitionFun
  g_self := A.transitionFun_self
  g_symm := A.transitionFun_symm
  g_trans := A.transitionFun_trans

/-- **PACKAGE A (item 15).**  The presentation-level transition system is *literally* the
inherited Task-XXVII one; nothing has been redefined. -/
theorem ordinarySystem_eq (F : BareMetricOrientedFamily B E)
    (A : OrdinaryAtlasPresentation F ι) :
    ordinarySystem A = (presentedFamily F A).toOrdinaryTransitionSystem := rfl

theorem toOrdinaryTransitionSystem_eq (T : TopologicalFrameFamily B E ι) :
    T.toOrdinaryTransitionSystem = ordinarySystem (presentationOf T) := rfl

@[simp] theorem ordinarySystem_U {F : BareMetricOrientedFamily B E}
    (A : OrdinaryAtlasPresentation F ι) (i : ι) : (ordinarySystem A).U i = A.U i := rfl

@[simp] theorem ordinarySystem_g {F : BareMetricOrientedFamily B E}
    (A : OrdinaryAtlasPresentation F ι) (i j : ι) (x : ↥(A.U i ∩ A.U j)) :
    (ordinarySystem A).g i j x = A.transitionFun i j x := rfl

end Bare

end NullSectorTask32
