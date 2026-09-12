import RequestProject.Spine.E2.Defect.ExistenceClassification

/-!
# Task 31, Packages N, Q and R: the closure verdict and the frozen spatial interface

**Items 92–93 (verdict), 103–106 (interface), 107–110 (boundary).**

## Package N — the closure verdict

The three admissible verdicts are represented by `ClosureStatus`.  The verdict of Task XXXI
is recorded formally as `spatialClosureVerdict` and justified by
`spatialClosureVerdict_justified`:

* universal existence is **refuted** — an explicit inherited-class ordinary transition system
  with unsolvable kernel equations is constructed (Package F);
* liftability is nevertheless **exactly classified** — it is equivalent to neutrality of the
  intrinsic global kernel-defect state (Package J);
* a positive example exists as well, so neither branch is vacuous.

This is Verdict **N** of the required table, strengthened by the full classification of
Verdict C.  No ambiguous language is used anywhere.

## Package Q — the frozen spatial interface

`SpatialInternalLiftClosure` bundles exactly what has been proved for one ordinary transition
system, one frozen internal projection and one inherited ordinary frame side: the
liftability/neutrality equivalence, the conditional global construction with its surjective
equivariant map and exact kernel fibres, and the closure status.  It is **not** merged with
the longitudinal Lorentz branch (item 106): nothing of the split-complex development is
mentioned here.

## Package R — the exact boundary (item 108)

Formally proved in this layer: only the statements listed in the interface below.  Explicitly
**absent**, and nowhere asserted: any 3+1 Lorentzian spin structure, any soldering of the
internal object to spacetime tangent fibres, any reconstruction of a Lorentz metric from the
spatial lift, any relativity axioms, any connection, curvature or dynamics.  The interface
question of item 109 — whether the metric-oriented spatial carrier used here is canonically
identifiable with the spatial sector of the longitudinal split-complex development — is
**not answered** in Task XXXI and is not stated as a theorem anywhere.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t y z

/-! ## Package N — the verdict -/

/-- **PACKAGE N (item 93).**  The three admissible closure verdicts of Task XXXI. -/
inductive ClosureStatus where
  /-- Verdict P: every inherited ordinary system is liftable. -/
  | universalExistence : ClosureStatus
  /-- Verdict C: liftability is exactly classified, with no example either way. -/
  | classifiedConditionalExistence : ClosureStatus
  /-- Verdict N: universal existence is refuted by an explicit inherited-class instance. -/
  | explicitNonexistenceForSomeInstances : ClosureStatus
  deriving DecidableEq, Repr

/-- **PACKAGE N (item 93), THE FORMAL VERDICT OF TASK XXXI.** -/
def spatialClosureVerdict : ClosureStatus :=
  ClosureStatus.explicitNonexistenceForSomeInstances

/-- **PACKAGE N (item 93), the justification of the verdict, in one statement.**  For every
internal projection over the visible model group without a whole-domain internal
representative of the identity: universal liftability is false, an explicit non-liftable
ordinary system exists, an explicit liftable one exists, and liftability is exactly
neutrality of the intrinsic global kernel-defect state. -/
theorem spatialClosureVerdict_justified {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel)
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    spatialClosureVerdict = ClosureStatus.explicitNonexistenceForSomeInstances ∧
      ¬ UniversalInternalLiftability P ∧
      (∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
          (S : NullSectorTask28.OrdinaryTransitionSystem B ι), ¬ OrdinaryInternalLiftable P S) ∧
      (∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
          (S : NullSectorTask28.OrdinaryTransitionSystem B ι), OrdinaryInternalLiftable P S) ∧
      (∀ (B : Type) [TopologicalSpace B] (ι : Type)
          (S : NullSectorTask28.OrdinaryTransitionSystem B ι),
          OrdinaryInternalLiftable P S ↔ IsNeutralGlobalKernelDefect P (ofOrdinary S)) :=
  ⟨rfl, not_universalInternalLiftability P hP,
    exists_ordinary_system_not_internalLiftable P hP,
    exists_ordinary_system_internalLiftable P,
    fun _ _ _ _ => internalLiftable_iff_globalKernelDefect_neutral⟩

/-! ## Package Q — the frozen spatial closure interface -/

section Interface

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm]

/-- **PACKAGE Q (items 103–105), principal interface.**  The frozen closure of the spatial
branch for one ordinary transition system, one frozen internal projection and one inherited
ordinary frame side.  Every field is a theorem proved in this task; nothing else is
exported. -/
structure SpatialInternalLiftClosure (P : InternalProjection L G)
    (S : TransitionSystem B ι G) (M : OrdinaryFrameModel G Fm) {Tot : Type y}
    [TopologicalSpace Tot] (F : OrdinaryFrameSide S M Tot) where
  /-- The exact existence classification. -/
  liftable_iff_neutral : InternalLiftable P S ↔ IsNeutralGlobalKernelDefect P S
  /-- Neutrality is a property of the ordinary system, independent of every auxiliary
  choice. -/
  neutrality_intrinsic : ∀ C C' : InternalTransitionCandidate P S,
    IsNeutralDefectState C ↔ IsNeutralDefectState C'
  /-- The global construction, with the surjective equivariant map and the exact kernel
  fibres. -/
  neutral_constructs_global : IsNeutralGlobalKernelDefect P S →
    ∃ (E : Type max u w t) (_ : TopologicalSpace E) (Q : GluedInternalFrameSystem P S M F E),
      Function.Surjective Q.toFrame ∧
        (∀ (x : E) (a : L), Q.toFrame (Q.act x a) = F.ract (Q.toFrame x) (P.proj a)) ∧
        (∀ x y : E, Q.base x = Q.base y → ∃! a : L, Q.act x a = y) ∧
        (∀ y : Tot, (∃ x : E, Q.toFrame x = y) ∧
          ∀ x x' : E, Q.toFrame x = y → Q.toFrame x' = y →
            ∃! z : P.Ker, Q.act x (z : L) = x') ∧
        (Nat.card P.Ker = 2 → ∀ y : Tot, Nat.card {x : E // Q.toFrame x = y} = 2)
  /-- The closure status of the whole spatial branch. -/
  status : ClosureStatus

/-- **PACKAGE Q (items 103–105), the interface is inhabited by the proved results.** -/
def spatialInternalLiftClosure (P : InternalProjection L G) (S : TransitionSystem B ι G)
    (M : OrdinaryFrameModel G Fm) {Tot : Type y} [TopologicalSpace Tot]
    (F : OrdinaryFrameSide S M Tot) : SpatialInternalLiftClosure P S M F where
  liftable_iff_neutral := internalLiftable_iff_globalKernelDefect_neutral
  neutrality_intrinsic := isNeutralDefectState_rep_choice_independent
  neutral_constructs_global := neutralDefect_constructs_globalTwofoldInternalFrameLift F
  status := spatialClosureVerdict

/-- **PACKAGE Q (item 105).**  The status carried by the frozen interface is the Task-XXXI
verdict. -/
@[simp] theorem spatialInternalLiftClosure_status (P : InternalProjection L G)
    (S : TransitionSystem B ι G) (M : OrdinaryFrameModel G Fm) {Tot : Type y}
    [TopologicalSpace Tot] (F : OrdinaryFrameSide S M Tot) :
    (spatialInternalLiftClosure P S M F).status =
      ClosureStatus.explicitNonexistenceForSomeInstances := rfl

end Interface

end NullSectorTask31
