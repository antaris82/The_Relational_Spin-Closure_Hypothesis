import RequestProject.Spine.E2.Cech.Cover

/-!
# Task 3, WP3 : local Spin lifts of the visible transition data

The inherited local-section property of an `InternalProjection` says that **every point of
the visible group** `G` has a neighbourhood carrying a continuous section of the projection.
It does *not* say that a given transition map `g_ij : U_ij → G` has a continuous lift on the
*whole* overlap `U_ij`, and nothing in this file pretends otherwise.

What is proved here:

* `isInternalRepOn_of_mapsTo_section` — the exact sufficient condition: if `g` is continuous
  on `V` and maps `V` into the domain `W` of a continuous section `s`, then `s ∘ g` is a
  continuous lift of `g` on `V`.  **DERIVED_NATIVE.**
* `exists_lift_nhdsWithin` — the unconditional *local* statement: every point of the overlap
  has a relative neighbourhood on which a continuous lift exists.  **DERIVED_NATIVE.**
* `SpinLiftFamily` — the data of one continuous lift per ordered pair of indices, on the
  whole double overlap, and the predicate `IsLiftAdmissible` asserting that such lifts exist.
  Whether a given cover is lift-admissible is *not* asserted; it is a hypothesis of every
  later theorem.  **CHOICE_UP_TO_KERNEL** (the family itself is a choice; the ambiguity is
  computed in `Coboundary.lean`).
* `isLiftAdmissible_of_sectionDomains` — a cover whose transition maps land in
  section domains is lift-admissible.  **ADDITIONAL_ASSUMPTION**, explicitly classified.
* `isLiftAdmissible_of_locally_const` — the transition maps that are constant on each overlap
  are always liftable (a non-vacuity witness).  **DERIVED_NATIVE.**
* `CoverRefinement.isLiftAdmissible_of_fine` — the WP3 refinement statement in the exact form
  the present topology supports: a refinement all of whose double overlaps are mapped into
  section domains carries lifts of the pulled-back transition data.  **ADDITIONAL_ASSUMPTION
  / COVER_REFINEMENT_DEPENDENT.**

What is **not** proved, and is recorded as the first exact obstruction of Task 3 (see
`TASK03_AUDIT.md`): that *every* cover of *every* topological base admits a lift-admissible
refinement.  Producing one requires shrinking the patches of the cover simultaneously for all
index pairs, which needs an extra hypothesis on the base (paracompactness / a shrinking
lemma, or a good cover), or a covering-space lifting criterion on the overlaps.  No such
hypothesis is smuggled in anywhere below.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace CechSpinLift

open NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}

/-! ## The sufficient condition for a lift on a whole overlap -/

/-- **DERIVED_NATIVE (WP3).**  If the visible map `g` is continuous on `V` and takes its
values in the domain `W` of a continuous section `s` of the projection, then `s ∘ g` is a
continuous internal (Spin-side) representative of `g` on all of `V`. -/
theorem isInternalRepOn_of_mapsTo_section (P : InternalProjection L G) {g : X → G} {V : Set X}
    (hg : ContinuousOn g V) {W : Set G} {s : G → L} (hs : ContinuousOn s W)
    (hsec : ∀ y ∈ W, P.proj (s y) = y) (hmap : Set.MapsTo g V W) :
    P.IsInternalRepOn g V (fun x => s (g x)) :=
  ⟨hs.comp hg hmap, fun x hx => hsec (g x) (hmap hx)⟩

/-- **DERIVED_NATIVE (WP3).**  Unconditional *local* liftability: every point of the domain
of a map continuous on `V` has a relative neighbourhood inside `V` on which a continuous lift
exists.  This is the strongest statement available with no hypothesis on the base, and it is
exactly what fails to give a lift on the whole overlap. -/
theorem exists_lift_nhdsWithin (P : InternalProjection L G) {g : X → G} {V : Set X}
    (hg : ContinuousOn g V) {x : X} (hx : x ∈ V) :
    ∃ N ∈ nhdsWithin x V, N ⊆ V ∧ ∃ u : X → L, P.IsInternalRepOn g N u := by
  obtain ⟨W, hWopen, hxW, s, hs, hsec⟩ := P.hasLocalSection (g x)
  refine ⟨V ∩ g ⁻¹' W, ?_, Set.inter_subset_left, fun y => s (g y), ?_⟩
  · exact Filter.inter_mem self_mem_nhdsWithin
      ((hg x hx).preimage_mem_nhdsWithin (hWopen.mem_nhds hxW))
  · exact isInternalRepOn_of_mapsTo_section P (hg.mono Set.inter_subset_left) hs hsec
      fun _ hy => hy.2

/-! ## Families of local lifts on a cover -/

variable {𝓤 : CechCover X ι}

/-- **NEWLY DEFINED (WP3), principal.**  A family of continuous internal (Spin-side) lifts of
the visible transition data: one lift per ordered pair of indices, defined and continuous on
the whole double overlap, projecting onto the visible transition map.

The family is a *choice*: nothing here fixes it, and `Coboundary.lean` computes exactly how
much it can vary. -/
structure SpinLiftFamily (P : InternalProjection L G) (T : VisibleCocycle G 𝓤) where
  /-- The chosen lift of `g i j`. -/
  lift : ι → ι → (X → L)
  /-- Each chosen lift is a continuous internal representative on the double overlap. -/
  isRep : ∀ i j, P.IsInternalRepOn (T.g i j) (𝓤.overlap₂ i j) (lift i j)

/-- **NEWLY DEFINED (WP3).**  The visible transition data is *lift-admissible* on the given
cover when every transition map has a continuous lift on the whole double overlap.  This is a
hypothesis, never a theorem, in the abstract setting. -/
def IsLiftAdmissible (P : InternalProjection L G) (T : VisibleCocycle G 𝓤) : Prop :=
  ∀ i j, ∃ u : X → L, P.IsInternalRepOn (T.g i j) (𝓤.overlap₂ i j) u

/-- **DERIVED_NATIVE (WP3).**  Lift-admissibility is exactly the existence of a lift family;
the passage from the predicate to the family is the only place where a choice is made. -/
theorem nonempty_spinLiftFamily_iff (P : InternalProjection L G) (T : VisibleCocycle G 𝓤) :
    Nonempty (SpinLiftFamily P T) ↔ IsLiftAdmissible P T := by
  constructor
  · rintro ⟨D⟩ i j
    exact ⟨D.lift i j, D.isRep i j⟩
  · intro h
    exact ⟨⟨fun i j => (h i j).choose, fun i j => (h i j).choose_spec⟩⟩

/-- **ADDITIONAL_ASSUMPTION (WP3).**  A cover whose transition maps take their values in
domains of continuous local sections is lift-admissible.  The hypothesis is a genuine extra
assumption on the pair (cover, transition data); it is *not* automatic. -/
theorem isLiftAdmissible_of_sectionDomains (P : InternalProjection L G)
    (T : VisibleCocycle G 𝓤)
    (h : ∀ i j, ∃ W : Set G, ∃ s : G → L, ContinuousOn s W ∧ (∀ y ∈ W, P.proj (s y) = y) ∧
      Set.MapsTo (T.g i j) (𝓤.overlap₂ i j) W) :
    IsLiftAdmissible P T := by
  intro i j
  obtain ⟨W, s, hs, hsec, hmap⟩ := h i j
  exact ⟨fun x => s (T.g i j x),
    isInternalRepOn_of_mapsTo_section P (T.continuousOn_g i j) hs hsec hmap⟩

/-- **DERIVED_NATIVE (WP3), non-vacuity witness.**  Visible transition data which is constant
on each double overlap is always lift-admissible: surjectivity of the projection provides a
constant lift.  No section, and no hypothesis on the base, is needed. -/
theorem isLiftAdmissible_of_const (P : InternalProjection L G) (T : VisibleCocycle G 𝓤)
    (h : ∀ i j, ∃ c : G, ∀ x ∈ 𝓤.overlap₂ i j, T.g i j x = c) :
    IsLiftAdmissible P T := by
  intro i j
  obtain ⟨c, hc⟩ := h i j
  obtain ⟨l, hl⟩ := P.surjective_proj c
  exact ⟨fun _ => l, continuousOn_const, fun x hx => by rw [hl, hc x hx]⟩

/-! ## The refinement form of WP3 -/

variable {ι' : Type t} {𝓥 : CechCover X ι'}

/-- **COVER_REFINEMENT_DEPENDENT / ADDITIONAL_ASSUMPTION (WP3).**  If a refinement `𝓥 → 𝓤` is
*fine* — every refined double overlap is mapped by the corresponding visible transition into
the domain of a continuous local section — then the pulled-back transition data is
lift-admissible on `𝓥`, so continuous lifts `g̃_ab : V_ab → L` with `ρ (g̃_ab) = g_{r a, r b}`
exist.

The fineness hypothesis is exactly the part which the present abstract topology does *not*
provide for free; see the audit. -/
theorem CoverRefinement.isLiftAdmissible_of_fine (P : InternalProjection L G)
    (T : VisibleCocycle G 𝓤) (R : CoverRefinement 𝓥 𝓤)
    (hfine : ∀ a b, ∃ W : Set G, ∃ s : G → L, ContinuousOn s W ∧
      (∀ y ∈ W, P.proj (s y) = y) ∧ Set.MapsTo (T.g (R.r a) (R.r b)) (𝓥.overlap₂ a b) W) :
    IsLiftAdmissible P (R.pullback T) :=
  isLiftAdmissible_of_sectionDomains P (R.pullback T) hfine

end CechSpinLift
