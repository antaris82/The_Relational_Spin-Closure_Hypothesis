import RequestProject.Spine.E2.AtlasChange.OrdinaryAtlasEquivalence

/-!
# Task 32, Package F: direct-atlas liftability versus family liftability

**HARD TARGET B, first step (items 48–54).**

* `DirectAtlasLiftable A` (item 48) is the Task-XXXI notion, re-exposed semantically: the
  ordinary transition system *of the chosen atlas* is Task-XXXI `InternalLiftable`.  The
  previous definition is untouched; this is an interface.
* `FamilyLiftable F` (item 49) is the family-level predicate: **some** admissible ordinary
  atlas presentation of the bare family `F` is directly liftable.

By construction `FamilyLiftable` mentions no atlas, so it depends only on the bare family
(item 51).  The two are then separated by the mandatory Task-XXXI control, which is proved in
`GoodBadAtlasComparison`.

Also proved here: liftability transfers along an ordinary cover refinement in the easy
direction (Package H, item 61) — and its converse is **refuted** in `GoodBadAtlasComparison`
by an explicit ordinary refinement of the Task-XXXI bad atlas.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask31

universe u v t k

/-! ## Transition-system level: refinement of an abstract ordinary transition system -/

section AbstractRefinement

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {κ : Type k} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type _} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- **PACKAGE H.**  The ordinary transition system obtained by restricting an abstract
transition system to a refinement of its cover. -/
def refinedSystem (S : TransitionSystem B ι G) (r : κ → ι) (V : κ → Set B)
    (hV : ∀ a, IsOpen (V a)) (hcov : ∀ b : B, ∃ a, b ∈ V a) (hsub : ∀ a, V a ⊆ S.U (r a)) :
    TransitionSystem B κ G where
  U := V
  isOpen_U := hV
  cover := hcov
  g := fun a c x => S.g (r a) (r c) ⟨(x : B), hsub a x.2.1, hsub c x.2.2⟩
  continuous_g := fun a c =>
    (S.continuous_g (r a) (r c)).comp (Continuous.subtype_mk continuous_subtype_val _)
  g_self := fun a x => S.g_self (r a) ⟨(x : B), hsub a x.2.1, hsub a x.2.2⟩
  g_symm := fun a c b h h' =>
    S.g_symm (r a) (r c) b ⟨hsub a h.1, hsub c h.2⟩ ⟨hsub c h'.1, hsub a h'.2⟩
  g_trans := fun a c d b h₁ h₂ h₃ =>
    S.g_trans (r a) (r c) (r d) b ⟨hsub a h₁.1, hsub d h₁.2⟩ ⟨hsub c h₂.1, hsub d h₂.2⟩
      ⟨hsub a h₃.1, hsub c h₃.2⟩

/-- **PACKAGE H (item 61), REQUIRED ENDPOINT (abstract form).**  Liftability passes to any
restriction of the cover: the internal transitions simply restrict. -/
theorem internalLiftable_refinedSystem {P : InternalProjection L G} {S : TransitionSystem B ι G}
    (r : κ → ι) (V : κ → Set B) (hV : ∀ a, IsOpen (V a)) (hcov : ∀ b : B, ∃ a, b ∈ V a)
    (hsub : ∀ a, V a ⊆ S.U (r a)) (h : InternalLiftable P S) :
    InternalLiftable P (refinedSystem S r V hV hcov hsub) := by
  obtain ⟨T⟩ := h
  exact ⟨{ v := fun a c x => T.v (r a) (r c) ⟨(x : B), hsub a x.2.1, hsub c x.2.2⟩
           continuous_v := fun a c =>
             (T.continuous_v (r a) (r c)).comp (Continuous.subtype_mk continuous_subtype_val _)
           proj_v := fun a c x =>
             T.proj_v (r a) (r c) ⟨(x : B), hsub a x.2.1, hsub c x.2.2⟩
           v_self := fun a x => T.v_self (r a) ⟨(x : B), hsub a x.2.1, hsub a x.2.2⟩
           v_symm := fun a c x => T.v_symm (r a) (r c) ⟨(x : B), hsub a x.2.1, hsub c x.2.2⟩
           v_trans := fun a c d x =>
             T.v_trans (r a) (r c) (r d)
               ⟨(x : B), ⟨hsub a x.2.1.1, hsub c x.2.1.2⟩, hsub d x.2.2⟩ }⟩

end AbstractRefinement

/-! ## Presentation-level liftability -/

section Liftability

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E} {ι : Type t} {κ : Type t}
  {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L GvisModel)

/-- **PACKAGE F (item 48), principal definition (interface, not a redefinition).**  An ordinary
atlas presentation is *directly liftable* when its own ordinary transition system is Task-XXXI
internally liftable. -/
def DirectAtlasLiftable (A : OrdinaryAtlasPresentation F ι) : Prop :=
  OrdinaryInternalLiftable P (ordinarySystem A)

theorem directAtlasLiftable_iff (A : OrdinaryAtlasPresentation F ι) :
    DirectAtlasLiftable P A ↔ InternalLiftable P (ofOrdinary (ordinarySystem A)) :=
  Iff.rfl

/-- **PACKAGE F.**  Direct liftability of the presentation of an inherited Task-XXVII frame
family is exactly Task-XXXI liftability of its inherited transition system. -/
theorem directAtlasLiftable_presentationOf (T : TopologicalFrameFamily B E ι) :
    DirectAtlasLiftable P (presentationOf T) ↔
      OrdinaryInternalLiftable P T.toOrdinaryTransitionSystem :=
  Iff.rfl

/-- **PACKAGE F (item 49), principal definition.**  The family-level liftability predicate:
*some* admissible ordinary atlas presentation of the bare family is directly liftable.  The
statement mentions no atlas, hence (item 51) depends only on the bare family. -/
def FamilyLiftable (F : BareMetricOrientedFamily B E) : Prop :=
  ∃ (ι : Type t) (A : OrdinaryAtlasPresentation F ι), DirectAtlasLiftable P A

/-- **PACKAGE F (item 19 of the endpoint list).**  A directly liftable atlas witnesses family
liftability. -/
theorem familyLiftable_of_directAtlasLiftable {A : OrdinaryAtlasPresentation F ι}
    (h : DirectAtlasLiftable P A) : FamilyLiftable.{u, v, t} P F :=
  ⟨ι, A, h⟩

/-- **PACKAGE F (item 51).**  Family liftability is a property of the bare family: two
inherited frame families with the same bare layer have the same family-level verdict. -/
theorem familyLiftable_depends_only_on_bare {T T' : TopologicalFrameFamily B E ι}
    (h : bareOf T = bareOf T') :
    FamilyLiftable.{u, v, t} P (bareOf T) ↔ FamilyLiftable.{u, v, t} P (bareOf T') := by
  rw [h]

/-! ## Behaviour under ordinary cover refinement -/

/-- **PACKAGE H (item 61), REQUIRED ENDPOINT.**  Direct liftability passes to every ordinary
cover refinement. -/
theorem directAtlasLiftable_refine {A : OrdinaryAtlasPresentation F ι}
    (R : OrdinaryCoverRefinement A κ) (h : DirectAtlasLiftable P A) :
    DirectAtlasLiftable P R.atlas :=
  internalLiftable_refinedSystem (P := P)
    (S := ofOrdinary (ordinarySystem A)) R.r R.V R.isOpen_V R.cover_V R.subset h

/-- **PACKAGE H (item 65), principal definition.**  An atlas is *refinement liftable* when
some ordinary refinement of it is directly liftable. -/
def RefinementLiftable (A : OrdinaryAtlasPresentation F ι) : Prop :=
  ∃ (κ : Type t) (R : OrdinaryCoverRefinement A κ), DirectAtlasLiftable P R.atlas

/-- **PACKAGE H.**  Direct liftability implies refinement liftability (identity refinement). -/
theorem refinementLiftable_of_directAtlasLiftable {A : OrdinaryAtlasPresentation F ι}
    (h : DirectAtlasLiftable P A) : RefinementLiftable.{u, v, t} P A :=
  ⟨ι, OrdinaryCoverRefinement.idRefinement A, h⟩

/-- **PACKAGE H (item 67), REQUIRED ENDPOINT.**  Refinement liftability of any atlas of a bare
family implies family liftability. -/
theorem familyLiftable_of_refinementLiftable {A : OrdinaryAtlasPresentation F ι}
    (h : RefinementLiftable.{u, v, t} P A) : FamilyLiftable.{u, v, t} P F := by
  obtain ⟨κ, R, hR⟩ := h
  exact ⟨κ, R.atlas, hR⟩

/-- **PACKAGE H (item 66), the direction that is proved.**  Refinement liftability of a
refinement implies refinement liftability of the original atlas, because a refinement of a
refinement is a refinement with the *same* refined atlas. -/
theorem refinementLiftable_of_refine {A : OrdinaryAtlasPresentation F ι}
    (R : OrdinaryCoverRefinement A κ) (h : RefinementLiftable.{u, v, t} P R.atlas) :
    RefinementLiftable.{u, v, t} P A := by
  obtain ⟨κ', R', hR'⟩ := h
  exact ⟨κ', R.comp R', hR'⟩

end Liftability

end NullSectorTask32
