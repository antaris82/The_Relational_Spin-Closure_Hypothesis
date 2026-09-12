import RequestProject.Spine.E2.AtlasChange.FamilyDefectNeutrality

/-!
# Task 32, Packages M, N, O, P: the family-level existence verdict

**HARD TARGET C (items 90–101), Package O (the outcome trichotomy) and Package P (the
conditional global object).**

* `UniversalFamilyLiftability` (item 90) is *stated* for the full inherited class of bare
  metric-oriented rank-three families.  It is **neither proved nor refuted** here.  Item 91 is
  respected: the Task-XXXI bad presentation says nothing about it, and indeed
  `GoodBad.badFamilyBase_familyLiftable` shows that the Task-XXXI family is *positive* evidence
  rather than a counterexample.
* Item 99/101: no genuine family-level negative example is produced.  Constructing one would
  require an invariant surviving *all* admissible ordinary presentations and refinements, which
  within the reconstructed layer is exactly the point at which standard obstruction theory
  would have to be imported — forbidden by the firewall.  The stop-on-hard-frontier rule is
  therefore applied and the outcome is **Verdict C**.
* Package P (items 102–105): family-level neutrality does produce, for a suitable presentation,
  the complete Task-XXX global glued internal object with surjective equivariant map and exact
  two-point kernel fibres.  Item 106 is applied to the *uniqueness* question across different
  liftable presentations: it is explicitly deferred, not claimed.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30
open NullSectorTask31

universe u v t y z

/-! ## Package P — the conditional global object at family level -/

section GlobalObject

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E}
  {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L GvisModel)

/-- **PACKAGE P (items 102–103), REQUIRED ENDPOINT.**  If the bare family is family-level
liftable then *some* ordinary atlas presentation of it carries the complete Task-XXX global
glued internal object: a locally trivial internal total space with a continuous free fibrewise
transitive right internal action, a continuous surjective equivariant map onto the ordinary
frame total space of that presentation, exact kernel fibres and — for the certified
two-element kernel — exactly two points per fibre. -/
theorem familyLiftable_constructs_globalTwofoldInternalFrameLift
    {Fm : Type z} [TopologicalSpace Fm] [MulAction GvisModel Fm]
    (M : OrdinaryFrameModel GvisModel Fm) {Tot : Type y} [TopologicalSpace Tot]
    (h : FamilyLiftable.{u, v, t} P F) :
    ∃ (ι₀ : Type t) (A : OrdinaryAtlasPresentation F ι₀),
      DirectAtlasLiftable P A ∧
      ∀ FS : OrdinaryFrameSide (ofOrdinary (ordinarySystem A)) M Tot,
        ∃ (Etot : Type (max u t)) (_ : TopologicalSpace Etot)
          (Q : GluedInternalFrameSystem P
            (ofOrdinary (ordinarySystem A)) M FS Etot),
          Function.Surjective Q.toFrame ∧
          (∀ y : Tot, (∃ x : Etot, Q.toFrame x = y) ∧
            ∀ x x' : Etot, Q.toFrame x = y → Q.toFrame x' = y →
              ∃! z : P.Ker, Q.act x ↑z = x') ∧
          (Nat.card P.Ker = 2 →
            ∀ y : Tot, Nat.card {x : Etot // Q.toFrame x = y} = 2) := by
  obtain ⟨ι₀, A, hA⟩ := h
  refine ⟨ι₀, A, hA, fun FS => ?_⟩
  obtain ⟨Etot, inst, Q, hsurj, _heq, _htors, hfib, hcard⟩ :=
    neutralDefect_constructs_globalTwofoldInternalFrameLift FS
      (internalLiftable_iff_globalKernelDefect_neutral.1 hA)
  exact ⟨Etot, inst, Q, hsurj, hfib, hcard⟩

end GlobalObject

/-! ## Packages M, N, O — the family-level existence verdict -/

section Verdict

/-- **PACKAGE M (item 90), the universal question, stated for the full inherited class.**
This proposition is deliberately left undecided by Task XXXII: it is neither proved nor
refuted below. -/
def UniversalFamilyLiftability {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel) : Prop :=
  ∀ (B : Type) [TopologicalSpace B] (E : B → Type) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] (F : BareMetricOrientedFamily B E),
    FamilyLiftable.{0, 0, 0} P F

/-- **PACKAGE O.**  The three admissible Task-XXXII outcomes. -/
inductive Task32Verdict
  /-- Verdict A: every inherited underlying family is family-level liftable. -/
  | presentationObstructionDisappears
  /-- Verdict B: a genuine atlas-independent non-liftable family exists. -/
  | genuineGeometricObstruction
  /-- Verdict C: the exact family-level classification is proved, examples unresolved. -/
  | classificationOnly
  deriving DecidableEq, Repr

/-- **PACKAGE O, the frozen Task-XXXII verdict.**  Verdict **C**: the exact family-level
classification is proved; neither universal family liftability nor a genuine
atlas-independent non-neutral family is established. -/
def task32_verdict : Task32Verdict := Task32Verdict.classificationOnly

/-- **PACKAGE O (item 101), the production part of the content of Verdict C.**

The exact family-level classification holds for every bare family of the inherited class.

The second half of the upstream statement — the concrete good/bad atlas evidence — is a
negative-control statement and lives in the control module
`RequestProject.Spine.Controls.E2.FamilyDefectControl` (`task32_verdictC_content`), which this
production module does not import. -/
theorem task32_verdictC_classification {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel) :
    ∀ {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
      [∀ b, InnerProductSpace ℝ (E b)] (F : BareMetricOrientedFamily B E),
        FamilyLiftable.{u, v, t} P F ↔ FamilyKernelDefectNeutral.{u, v, t} P F :=
  fun _ => familyLiftable_iff_familyKernelDefectNeutral P

end Verdict

end NullSectorTask32
