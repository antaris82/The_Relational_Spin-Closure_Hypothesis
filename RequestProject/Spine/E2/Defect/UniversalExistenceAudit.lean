import RequestProject.Spine.E2.Defect.GlobalMapHardening

/-!
# Task 31, Packages E and F: the universal existence audit and the explicit examples

**HARD TARGET B (items 43–56).**

Package E states the universal question explicitly (item 43):

> does *every* ordinary transition system satisfying the inherited Task-XXVII interface admit
> compatible continuous internal transitions through the certified internal projection?

The answer is **no**, and it is settled here by an explicit example internal to the
reconstruction (items 48–54).  The inherited assumptions are **not** strengthened anywhere
(item 45), and no standard obstruction theorem, characteristic class or non-spin manifold is
imported (items 52, 143).

## The negative example (Package F)

The base is the reconstructed visible model group itself, with the two-element index set and
the trivial cover `U₀ = U₁ = univ`.  The transitions are

```
g₀₀ = g₁₁ = 1,      g₀₁ (b) = b,      g₁₀ (b) = b⁻¹ .
```

All four inherited laws (continuity, identity, inverse, triple overlap) hold, so this is a
legitimate `OrdinaryTransitionSystem`, the frozen Task-XXVII output interface.

A compatible continuous internal transition system for it would consist, in particular, of a
continuous map `v₀₁` on the whole base with `proj (v₀₁ b) = b` — that is, a **continuous
global internal representative of the identity map of the visible group**.  The negative
statement is therefore proved *generically*, for every internal projection `P` admitting no
such whole-domain representative: `badSystem_not_internalLiftable`.  No concrete projection
is fixed anywhere in this module.

The impossibility proof is therefore elementary and internal: it uses only the explicit
transition data of the example and one inherited certified theorem about the projection
itself.  Nothing about bundles, cohomology or characteristic classes is used.

## The positive example (item 55)

Over the *same* base and the *same* cover, the system with all transitions equal to the
identity is liftable.  Consequently liftability is a genuine global property of the
transition system: neither automatic nor impossible (item 56).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u t

/-! ## Package E — the universal question -/

/-- **PACKAGE E (item 43).**  The universal existence question, stated explicitly: does every
ordinary transition system satisfying the inherited Task-XXVII interface admit compatible
continuous internal transitions through the certified internal projection? -/
def UniversalInternalLiftability {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L NullSectorTask26.GvisModel) : Prop :=
  ∀ (B : Type) [TopologicalSpace B] (ι : Type) (S : NullSectorTask28.OrdinaryTransitionSystem B ι),
    OrdinaryInternalLiftable P S

/-! ## Package F — the explicit examples -/

namespace Examples

/-- The transition maps of the explicit systems: the identity on one off-diagonal entry, its
inverse on the other, and the neutral element on the diagonal. -/
def badTrans (i j : Bool) (x : ↥GvisModel) : ↥GvisModel :=
  if i = j then 1 else if j then x else x⁻¹

@[simp] theorem badTrans_self (i : Bool) (x : ↥GvisModel) : badTrans i i x = 1 := by
  simp [badTrans]

@[simp] theorem badTrans_ft (x : ↥GvisModel) : badTrans false true x = x := by
  simp [badTrans]

@[simp] theorem badTrans_tf (x : ↥GvisModel) : badTrans true false x = x⁻¹ := by
  simp [badTrans]

/-- **PACKAGE F (item 50), the explicit negative test system.**  Base: the reconstructed
visible model group.  Cover: two copies of the whole base.  Transitions: the identity and its
inverse.  Every inherited law is verified below, so this is an instance of the frozen
Task-XXVII interface. -/
def badSystem : NullSectorTask28.OrdinaryTransitionSystem (↥GvisModel) Bool where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun b => ⟨false, Set.mem_univ b⟩
  g := fun i j x => badTrans i j (x : ↥GvisModel)
  continuous_g := by
    intro i j
    cases i <;> cases j <;>
      simp only [badTrans_self, badTrans_ft, badTrans_tf]
    · exact continuous_const
    · exact continuous_subtype_val
    · exact continuous_subtype_val.inv
    · exact continuous_const
  g_self := by intro i b; simp
  g_symm := by intro i j b h h'; cases i <;> cases j <;> simp
  g_trans := by intro i j k b h₁ h₂ h₃; cases i <;> cases j <;> cases k <;> simp

/-- **PACKAGE F (item 55), the explicit positive test system.**  The same base and the same
cover, with all transitions trivial. -/
def goodSystem : NullSectorTask28.OrdinaryTransitionSystem (↥GvisModel) Bool where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun b => ⟨false, Set.mem_univ b⟩
  g := fun _ _ _ => 1
  continuous_g := fun _ _ => continuous_const
  g_self := fun _ _ => rfl
  g_symm := fun _ _ _ _ _ => inv_one.symm
  g_trans := fun _ _ _ _ _ _ _ => (one_mul 1).symm

/-- **PACKAGE F (item 55), first half.**  The trivial system is internally liftable, through
*any* internal projection. -/
theorem goodSystem_internalLiftable {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L NullSectorTask26.GvisModel) :
    OrdinaryInternalLiftable P goodSystem :=
  internalLiftable_of_transitions_trivial (fun _ _ _ => rfl)

/-- **PACKAGE F (items 49–53), the impossibility theorem, generic form.**  For every internal
projection `P` that has **no** continuous internal representative of the identity over the
whole visible group, the explicit negative test system admits no compatible continuous
internal transitions.

The proof is elementary and internal: a compatible system would in particular provide such a
whole-domain representative.  No obstruction theory and no concrete model enter. -/
theorem badSystem_not_internalLiftable {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L NullSectorTask26.GvisModel)
    (hP : ¬ P.HasContinuousInternalRep (id : NullSectorTask26.GvisModel → _) Set.univ) :
    ¬ OrdinaryInternalLiftable P badSystem := by
  rintro ⟨T⟩
  refine hP ⟨fun b => T.v false true ⟨b, Set.mem_univ _, Set.mem_univ _⟩, ?_, ?_⟩
  · exact continuousOn_univ.2 ((T.continuous_v false true).comp
      (Continuous.subtype_mk continuous_id _))
  · intro b _
    exact (T.proj_v false true ⟨b, Set.mem_univ _, Set.mem_univ _⟩).trans (badTrans_ft b)

end Examples

/-! ## The verdicts of Packages E and F -/

section Verdicts

variable {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L NullSectorTask26.GvisModel)

/-- **PACKAGE F (item 54), REQUIRED ENDPOINT
`exists_ordinary_system_not_internalLiftable`.**  Whenever the internal projection has no
whole-domain internal representative of the identity, there is an ordinary transition system
whose internally derived kernel equations are unsolvable. -/
theorem exists_ordinary_system_not_internalLiftable
    (hP : ¬ P.HasContinuousInternalRep (id : NullSectorTask26.GvisModel → _) Set.univ) :
    ∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
      (S : NullSectorTask28.OrdinaryTransitionSystem B ι), ¬ OrdinaryInternalLiftable P S :=
  ⟨_, inferInstance, Bool, Examples.badSystem, Examples.badSystem_not_internalLiftable P hP⟩

/-- **PACKAGE F (item 55), REQUIRED ENDPOINT
`exists_ordinary_system_internalLiftable`.**  Unconditionally, some ordinary system is
liftable. -/
theorem exists_ordinary_system_internalLiftable :
    ∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
      (S : NullSectorTask28.OrdinaryTransitionSystem B ι), OrdinaryInternalLiftable P S :=
  ⟨_, inferInstance, Bool, Examples.goodSystem, Examples.goodSystem_internalLiftable P⟩

/-- **PACKAGE E (items 44, 48), THE VERDICT OF HARD TARGET B.**  Universal liftability is
**false** for every projection without a whole-domain representative of the identity: it is
refuted by an explicit system of the inherited class, not merely unproved. -/
theorem not_universalInternalLiftability
    (hP : ¬ P.HasContinuousInternalRep (id : NullSectorTask26.GvisModel → _) Set.univ) :
    ¬ UniversalInternalLiftability P := by
  intro h
  exact Examples.badSystem_not_internalLiftable P hP (h _ _ Examples.badSystem)

/-- **PACKAGE F (item 56).**  Liftability is a genuine global property of the ordinary
transition system: over one and the same base and one and the same cover it holds for some
systems and fails for others. -/
theorem internalLiftability_is_genuinely_global
    (hP : ¬ P.HasContinuousInternalRep (id : NullSectorTask26.GvisModel → _) Set.univ) :
    (∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
        (S : NullSectorTask28.OrdinaryTransitionSystem B ι), OrdinaryInternalLiftable P S) ∧
      ∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
        (S : NullSectorTask28.OrdinaryTransitionSystem B ι), ¬ OrdinaryInternalLiftable P S :=
  ⟨exists_ordinary_system_internalLiftable P,
    exists_ordinary_system_not_internalLiftable P hP⟩

end Verdicts

end NullSectorTask31
