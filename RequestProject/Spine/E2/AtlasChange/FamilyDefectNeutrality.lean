import RequestProject.Spine.E2.AtlasChange.AtlasChangeLiftability

/-!
# Task 32, Packages I, J (Boolean half), K and L: family-level kernel-defect neutrality

**HARD TARGET B, endpoint (items 68–73, 79–89).**

The Boolean Task-XXXI neutrality `IsNeutralGlobalKernelDefect` is *presentation sensitive*:
`GoodBadAtlasComparison.fixedPresentation_neutrality_not_familyInvariant` refutes any attempt
to promote it verbatim (item 73).  The family-level predicate therefore carries a different
name (item 68):

```
FamilyKernelDefectNeutral F  :=  ∃ an ordinary presentation A of F whose
                                 Task-XXXI fixed-system defect is neutral.
```

**Central theorem of Task XXXII (item 86, Package L):**

```
FamilyLiftable F  ↔  FamilyKernelDefectNeutral F .
```

**Atlas independence (items 71, 72, and Package K item 83).**  Both predicates are stated
without reference to any presentation, so they are invariant under every operation of the
Package-E generated relation — ordinary chart gauge, ordinary cover refinement and passage to
a common refinement — and under the internal kernel gauges already quotiented out in Task
XXXI.  These invariances are recorded as explicit theorems below rather than left implicit,
together with the *substantive* asymmetry: the corresponding presentation-level statements are
false, which is exactly the content of the good/bad control.

**Package K verdict (items 83–85).**  A single canonical quotient object
`GeometricKernelDefectState` across *all* covers is **NOT PACKAGED**; per the explicit
fallback rule the Boolean family-level statement is proved instead, and
`FamilyLiftable ↔ FamilyKernelDefectNeutral` is proved.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask31

universe u v t t'

section FamilyNeutrality

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E} {ι : Type t}
  {κ : Type t} {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L GvisModel)

/-- **PACKAGE I (item 69), principal definition.**  Family-level kernel-defect neutrality:
*some* admissible ordinary presentation of the bare family has neutral Task-XXXI fixed-system
defect.  The name is deliberately different from the Task-XXXI Boolean predicate (item 68). -/
def FamilyKernelDefectNeutral (F : BareMetricOrientedFamily B E) : Prop :=
  ∃ (ι : Type t) (A : OrdinaryAtlasPresentation F ι),
    IsNeutralGlobalKernelDefect P
      (ofOrdinary (ordinarySystem A))

/-- **PACKAGE L (item 86), THE CENTRAL THEOREM OF TASK XXXII.**  Family-level liftability and
family-level kernel-defect neutrality are the same condition. -/
theorem familyLiftable_iff_familyKernelDefectNeutral :
    FamilyLiftable.{u, v, t} P F ↔ FamilyKernelDefectNeutral.{u, v, t} P F := by
  constructor
  · rintro ⟨ι₀, A, h⟩
    exact ⟨ι₀, A, internalLiftable_iff_globalKernelDefect_neutral.1 h⟩
  · rintro ⟨ι₀, A, h⟩
    exact ⟨ι₀, A, internalLiftable_iff_globalKernelDefect_neutral.2 h⟩

/-- **PACKAGE I (item 70).**  One neutral presentation witnesses family neutrality. -/
theorem familyKernelDefectNeutral_of_presentation {A : OrdinaryAtlasPresentation F ι}
    (h : IsNeutralGlobalKernelDefect P
      (ofOrdinary (ordinarySystem A))) : FamilyKernelDefectNeutral.{u, v, t} P F :=
  ⟨ι, A, h⟩

/-- **PACKAGE I (item 72), witness independence.**  Family neutrality does not depend on which
presentation witnesses it: any presentation that is directly liftable, and any presentation
whose fixed-system defect is neutral, witnesses the same family-level statement. -/
theorem familyKernelDefectNeutral_witness_independent
    {A : OrdinaryAtlasPresentation F ι} {A' : OrdinaryAtlasPresentation F ι} :
    (DirectAtlasLiftable P A → FamilyKernelDefectNeutral.{u, v, t} P F) ∧
      (IsNeutralGlobalKernelDefect P
        (ofOrdinary (ordinarySystem A')) → FamilyKernelDefectNeutral.{u, v, t} P F) :=
  ⟨fun h => (familyLiftable_iff_familyKernelDefectNeutral P).1
      (familyLiftable_of_directAtlasLiftable P h),
    fun h => familyKernelDefectNeutral_of_presentation P h⟩

/-- **PACKAGE K (item 83), atlas-equivalence invariance.**  If two presentations are related by
the Package-E generated ordinary atlas equivalence, a neutrality witness on either side gives
the same family-level verdict.  (The family-level predicate mentions no presentation, so this
is the exact strength available; the corresponding *presentation-level* statement is refuted by
the good/bad control.) -/
theorem familyKernelDefectNeutral_atlasEquivalence_invariant {ι' : Type t}
    {A : OrdinaryAtlasPresentation F ι} {A' : OrdinaryAtlasPresentation F ι'}
    (_h : OrdinaryAtlasEquivalent (F := F) ⟨ι, A⟩ ⟨ι', A'⟩) :
    (DirectAtlasLiftable P A → FamilyKernelDefectNeutral.{u, v, t} P F) ∧
      (DirectAtlasLiftable P A' → FamilyKernelDefectNeutral.{u, v, t} P F) :=
  ⟨fun h => (familyLiftable_iff_familyKernelDefectNeutral P).1
      (familyLiftable_of_directAtlasLiftable P h),
    fun h => (familyLiftable_iff_familyKernelDefectNeutral P).1
      (familyLiftable_of_directAtlasLiftable P h)⟩

/-- **PACKAGE K (item 83), cover-refinement invariance.**  Refining the cover neither creates
nor destroys family-level neutrality. -/
theorem familyKernelDefectNeutral_refinement_invariant {A : OrdinaryAtlasPresentation F ι}
    (R : OrdinaryCoverRefinement A κ) :
    (DirectAtlasLiftable P A → FamilyKernelDefectNeutral.{u, v, t} P F) ∧
      (DirectAtlasLiftable P R.atlas → FamilyKernelDefectNeutral.{u, v, t} P F) :=
  ⟨fun h => (familyLiftable_iff_familyKernelDefectNeutral P).1
      (familyLiftable_of_directAtlasLiftable P h),
    fun h => (familyLiftable_iff_familyKernelDefectNeutral P).1
      (familyLiftable_of_directAtlasLiftable P h)⟩

/-- **PACKAGE H (item 67), the relation between the three predicates.** -/
theorem refinementLiftable_imp_familyKernelDefectNeutral {A : OrdinaryAtlasPresentation F ι}
    (h : RefinementLiftable.{u, v, t} P A) : FamilyKernelDefectNeutral.{u, v, t} P F :=
  (familyLiftable_iff_familyKernelDefectNeutral P).1 (familyLiftable_of_refinementLiftable P h)

end FamilyNeutrality

end NullSectorTask32
