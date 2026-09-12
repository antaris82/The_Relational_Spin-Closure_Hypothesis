import RequestProject.Spine.E2.Cech.Cover

/-!
# Spine / SpinNative : Spin-valued relational (gluing) data, with no visible input

This is the **first module of the Spin-native branch**.  Its whole purpose is to name, at the
lowest possible level, the object

> a continuous `Spin`-valued comparison datum `g̃_ij` on the double overlaps of a cover,
> satisfying the exact Čech 1-cocycle law on the triple overlaps,

*without* any prior `SO`-valued (visible) transition data, without a chosen lift, without a
defect and without an obstruction class.

## Provenance (audit, Task-30 §3)

The project already contains exactly this mathematical object: `CechSpinLift.VisibleCocycle`
of `RequestProject.Spine.E2.Cech.Cover` is stated for an *arbitrary* topological group and
never mentions the projection `ρ`.  Its name — "visible" — is historical: it records that in
the standard branch this structure is instantiated at the visible (ordinary/`SO`-side) group
`G`.  Nothing in the structure forces that reading, and instantiating it at the internal
(`Spin`-side) group `L` gives precisely the Spin-native gluing datum.

Therefore **no new structure is introduced here**: `NativeSpinTransitionData` is an
`abbrev` for the existing cocycle structure at the internal group.  The identity law
`g̃_ii = 1` and the inverse law `g̃_ji = (g̃_ij)⁻¹` are *not* fields; they are the already
derived theorems `VisibleCocycle.g_self` and `VisibleCocycle.g_symm`, re-exported below.

## What this module deliberately does not contain

No projection, no kernel, no local lift, no defect, no obstruction: the import closure of
this module contains none of `E2.Cech.Defect`, `E2.Cech.Coboundary`, `E2.Cech.Obstruction`,
`E2.Cech.SpinInstance` or `Geometry.SpinStructure`.  The Spin-native branch is thus
constructible without the standard `SO`-first machinery; see
`RequestProject.Spine.Comparison.SpinNativeVsSO` for the comparison layer, which is the only
place where the two branches meet.

## Local fibre versus gluing datum versus global coherence

The distinction demanded by the provenance audit is visible in the types:

* a *local* Spin element/fibre is a value in `L` (or a map `U i → L`) — it involves no pair
  of indices and says nothing about gluing;
* a *Spin-valued comparison datum* is the field `g` below, indexed by ordered **pairs**;
* *global coherence* is the field `cocycle`, an assumption on **triples** — it is a genuine
  additional condition, not a consequence of the fibres.
-/

namespace SpinNative

open CechSpinLift

universe u w t

/-- **EXPOSED, not newly defined (Task 30).**  Spin-native transition data on a cover:
continuous `L`-valued (internal, Spin-side) comparison maps on the double overlaps obeying
the exact Čech 1-cocycle law on the triple overlaps.

This is literally the existing `CechSpinLift.VisibleCocycle` structure instantiated at the
internal group; the abbreviation exists only to make the Spin-native reading of that
group-agnostic structure explicit.  No `SO`-valued datum and no projection occurs in it. -/
abbrev NativeSpinTransitionData (L : Type u) [Group L] [TopologicalSpace L] {X : Type w}
    [TopologicalSpace X] {ι : Type t} (𝓤 : CechCover X ι) : Type _ :=
  VisibleCocycle L 𝓤

variable {L : Type u} [Group L] [TopologicalSpace L] {X : Type w} [TopologicalSpace X]
  {ι : Type t} {𝓤 : CechCover X ι}

/-- **DERIVED (re-export).**  Spin-native transition data satisfies the identity, inverse and
triple-overlap laws.  Only the last is a field; the first two are the derived laws of the
underlying cocycle structure. -/
theorem native_transition_laws (S : NativeSpinTransitionData L 𝓤) :
    (∀ i, ∀ x ∈ 𝓤.U i, S.g i i x = 1) ∧
    (∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, S.g j i x = (S.g i j x)⁻¹) ∧
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, S.g i j x * S.g j k x = S.g i k x) :=
  S.visible_transition_laws

/-- **DERIVED.**  Transition data with the same comparison maps are equal: the remaining
fields are propositions. -/
theorem transitionData_ext {S S' : NativeSpinTransitionData L 𝓤} (h : S.g = S'.g) : S = S' := by
  cases S; cases S'; subst h; rfl

end SpinNative
