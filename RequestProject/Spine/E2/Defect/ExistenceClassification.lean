import RequestProject.Spine.E2.Defect.DefectNeutrality

/-!
# Task 31, Packages J (global half) and M: from neutrality to the global twofold object

**Items 79, 80, 89–91.**

Package J proved

```
InternalLiftable S  ↔  IsNeutralGlobalKernelDefect S .
```

Combining it with the Task-XXX conditional construction and with the Package-B hardening
gives the strongest valid global theorem of this task
(`neutralDefect_constructs_globalTwofoldInternalFrameLift`, item 90): neutrality of the
intrinsic state produces a global locally trivial internal total space with a continuous free
fibrewise transitive right `Lift` action, a **surjective** continuous equivariant map onto the
whole ordinary frame total space, and exact kernel fibres — two points per fibre for the
certified two-element kernel.

The reverse implication (item 91) is proved at exactly the strength Task XXX left available:
a global object **together with the adapted-chart datum** recovers compatible internal
transitions, hence neutrality.  Without that datum the interface does not determine the
projection of the recovered transitions, and no reverse implication is claimed
(negative control 113).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t y z e

section Classification

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {P : InternalProjection L G}
  {S : TransitionSystem B ι G} {M : OrdinaryFrameModel G Fm} {Tot : Type y}
  [TopologicalSpace Tot]

/-- **PACKAGE M (items 89, 90), REQUIRED ENDPOINT
`neutralDefect_constructs_globalTwofoldInternalFrameLift`.**  If the intrinsic global
kernel-defect state of the ordinary system is neutral, then a global glued internal object
exists over the inherited ordinary frame total space, and its global map is **surjective**,
equivariant through `proj`, with every fibre an exact kernel torsor — two points per fibre
whenever the kernel has two elements. -/
theorem neutralDefect_constructs_globalTwofoldInternalFrameLift
    (F : OrdinaryFrameSide S M Tot) (h : IsNeutralGlobalKernelDefect P S) :
    ∃ (E : Type max u w t) (_ : TopologicalSpace E) (Q : GluedInternalFrameSystem P S M F E),
      Function.Surjective Q.toFrame ∧
        (∀ (x : E) (a : L), Q.toFrame (Q.act x a) = F.ract (Q.toFrame x) (P.proj a)) ∧
        (∀ x y : E, Q.base x = Q.base y → ∃! a : L, Q.act x a = y) ∧
        (∀ y : Tot, (∃ x : E, Q.toFrame x = y) ∧
          ∀ x x' : E, Q.toFrame x = y → Q.toFrame x' = y →
            ∃! z : P.Ker, Q.act x (z : L) = x') ∧
        (Nat.card P.Ker = 2 → ∀ y : Tot, Nat.card {x : E // Q.toFrame x = y} = 2) := by
  obtain ⟨T⟩ := internalLiftable_iff_globalKernelDefect_neutral.2 h
  refine ⟨InternalTotal T, inferInstance,
    compatibleTransitions_construct_globalInternalFrameLift T F, ?_, ?_, ?_, ?_, ?_⟩
  · exact GluedInternalFrameSystem.toFrame_surjective _
  · exact (compatibleTransitions_construct_globalInternalFrameLift T F).toFrame_equivariant
  · exact (compatibleTransitions_construct_globalInternalFrameLift T F).act_existsUnique
  · exact fun y => GluedInternalFrameSystem.toFrame_fibre_torsor _ y
  · exact fun hker y => GluedInternalFrameSystem.toFrame_fibre_card_two _ y hker

/-- **PACKAGE M (item 91), the reverse implication at its proved strength.**  A global glued
internal object **with the Task-XXX adapted-chart datum** forces the intrinsic global
kernel-defect state to be neutral. -/
theorem globalObject_adaptedCharts_imp_neutralDefect {E : Type e} [TopologicalSpace E]
    {F : OrdinaryFrameSide S M Tot} (Q : GluedInternalFrameSystem P S M F E)
    (hA : Q.AdaptedCharts) : IsNeutralGlobalKernelDefect P S :=
  internalLiftable_iff_globalKernelDefect_neutral.1 ⟨Q.extractedTransitions hA⟩

/-- **PACKAGE J/M (item 79), the complete proved chain.**  For the inherited ordinary frame
side, the following are equivalent, and each implies the global construction:

* the intrinsic global kernel-defect state is neutral;
* compatible continuous internal transitions exist;
* the internally derived kernel equations of any (equivalently: some) candidate are
  solvable. -/
theorem spatial_existence_chain (C : InternalTransitionCandidate P S) :
    (IsNeutralGlobalKernelDefect P S ↔ InternalLiftable P S) ∧
      (InternalLiftable P S ↔ CanTrivialise C) ∧
      (InternalLiftable P S ↔ CanTrivialiseSimultaneously P S C) :=
  ⟨internalLiftable_iff_globalKernelDefect_neutral.symm,
    internalLiftable_iff_canTrivialise C,
    internalLiftable_iff_canTrivialiseSimultaneously C⟩

end Classification

end NullSectorTask31
