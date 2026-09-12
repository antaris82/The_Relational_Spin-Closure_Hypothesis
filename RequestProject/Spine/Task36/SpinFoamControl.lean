import RequestProject.Spine.Task36.SpinNotLorentz
import RequestProject.Spine.Task36.TrivialControl

/-!
# Task 36 / §14 : spin-labelled combinatorial data is a different category

**Task-36 gate-separation control.**

## The claim being tested

The external discussion contains the phrase "Spin Foams carry spin".  §14 asks that this be
kept strictly apart from

```text
    the tangent bundle of a smooth manifold carries a Spin structure.
```

## What is *not* claimed

No universal theorem is asserted here.  It is **false** that no object called a spin foam can
ever be built from, or used to encode, a manifold, and nothing of that kind is proved.  The
only target is the robustness statement of §14:

```text
    spin-labelled combinatorial data does not by itself imply
    a smooth manifold together with a tangent Spin structure.
```

## The control object

`Task36.SpinFoamLabels V` is a minimal spin-labelled combinatorial complex: a set of vertices
`V`, a symmetric adjacency relation, and a `SpinGroup`-valued label on every ordered pair.
There is **no** topology, no cover, no cocycle condition and no local model: the label field
is an arbitrary function, which is exactly the content of
`Task36.spinFoamLabels_unconstrained`.  Contrast `CechSpinLift.VisibleCocycle`, which is
defined over an actual open cover of an actual topological space and is required to be
continuous on the overlaps and to satisfy the triple-overlap cocycle law — the conditions that
carry all the global information in this project.

## The theorems

* `Task36.spinFoamLabels_unconstrained` — every labelling whatsoever underlies a spin foam:
  the labels satisfy no constraint, so they cannot encode a gluing condition.
* `Task36.spin_foam_labels_do_not_determine_solder` — for **every** spin foam, and every
  labelling, there is a base gluing whose emergent base is a smooth four-manifold carrying a
  regular solder, and another one, also a smooth four-manifold, carrying none, for any Spin
  seed.  The label data are therefore logically independent of the existence of
  `SmoothTangentSolderData`, hence of the tangent Spin structure the project builds.

That independence is the precise sense in which the spin labels of a combinatorial complex are
in a different category from a Spin structure on `TM`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

/-- **NEWLY DEFINED (Task 36), §14.**  A minimal spin-labelled combinatorial complex: vertices,
a symmetric adjacency relation, and an intrinsic-`SpinGroup` label on every ordered pair.

Deliberately absent, and this is the point of the control: a topology on `V`, an open cover,
a local model, a continuity requirement and a triple-overlap cocycle law. -/
structure SpinFoamLabels (V : Type) where
  /-- The adjacency relation of the complex. -/
  adj : V → V → Prop
  /-- Symmetry of adjacency. -/
  adj_symm : ∀ u v, adj u v → adj v u
  /-- The spin label of an ordered pair. -/
  label : V → V → ↥SpinGroup

/-- **DERIVED (Task 36), §14.**  The labels are completely unconstrained: any labelling of any
symmetric relation underlies a spin foam.  In particular the labels satisfy no cocycle,
continuity or gluing condition, so they cannot by themselves encode one. -/
theorem spinFoamLabels_unconstrained {V : Type} (adj : V → V → Prop)
    (hsymm : ∀ u v, adj u v → adj v u) (label : V → V → ↥SpinGroup) :
    ∃ F : SpinFoamLabels V, F.adj = adj ∧ F.label = label :=
  ⟨⟨adj, hsymm, label⟩, rfl, rfl⟩

/-- **NEWLY DEFINED (Task 36), PRINCIPAL §14 — the gate separation.**

For any spin-labelled combinatorial complex there exist, independently of its labels, both

* a base gluing whose emergent base is a `C^∞` four-manifold **with** a regular solder
  (the one-chart model), and
* a base gluing whose emergent base is a `C^∞` four-manifold **without** a regular solder for
  any native Spin seed (the orientation-reversing model).

Hence no spin-label datum determines whether the project's tangent Spin structure exists: the
combinatorial spin labels and `SmoothTangentSolderData` are logically independent. -/
theorem spin_foam_labels_do_not_determine_solder {V : Type} (_F : SpinFoamLabels V) :
    (IsManifold localModelI (⊤ : ℕ∞) (Space oneChartGluing) ∧
      Nonempty (SmoothTangentSolderData oneChartGluing oneChartSpin)) ∧
    (IsManifold localModelI (⊤ : ℕ∞) (Space moebiusGluing) ∧
      ∀ S : NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing),
        IsEmpty (SmoothTangentSolderData moebiusGluing S)) :=
  ⟨⟨oneChartGluing_isManifold, ⟨oneChartSolder⟩⟩,
   ⟨loopGluingOf_isManifold Unit LoopTwist.flip, orientation_reversing_gluing_no_solder⟩⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.SpinFoamLabels
#print axioms Task36.spinFoamLabels_unconstrained
#print axioms Task36.spin_foam_labels_do_not_determine_solder
