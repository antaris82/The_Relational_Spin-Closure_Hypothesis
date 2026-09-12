import RequestProject.Spine.E2.Lift.TransitionLiftBase

/-!
# Task 28, Packages C, D and L: local continuous internal representatives

**HARD TARGET A.**

Given a frozen internal projection `P : InternalProjection L G` and *any* continuous map
`g : X → G` from a topological space, we prove:

* `exists_local_continuous_internal_rep` (item 32): every point of `X` has an open
  neighbourhood on which `g` admits a continuous internal representative.  The proof is
  exactly the preferred route of item 30 — a certified local section of `proj` around
  `g x`, the preimage of its domain, and the composite.  No choice function is used to
  select representatives pointwise (item 31).
* Package D (items 35–40): a neutral refinement structure `OverlapRefinement` for the
  domain, built from the local result, storing on each refined domain a continuous
  representative.  A representative on the *whole* domain is **not** required, and the
  special case in which one exists is recorded separately (item 40).
* Package L (items 89–95): the bounded diagnostic `HasContinuousInternalRep`, local
  existence everywhere, and the explicit statement that whole-domain existence is a strictly
  additional condition.  A concrete refutation is given for a native instance, in
  `RequestProject.Spine.Controls.CircleDoubleCover`, not here.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v w

namespace InternalProjection

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G]

/-! ## Package C — the local problem, formulated abstractly (item 28) -/

/-- **NEWLY DEFINED (items 28, 89).**  `u` is a continuous internal representative of the
ordinary map `g` on the subset `V`: it is continuous there and projects onto `g`. -/
def IsInternalRepOn {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)
    (g : X → G) (V : Set X) (u : X → L) : Prop :=
  ContinuousOn u V ∧ ∀ x ∈ V, P.proj (u x) = g x

/-- **NEWLY DEFINED (item 89), the bounded diagnostic of Package L.**  The ordinary map `g`
has a continuous internal representative over `V`. -/
def HasContinuousInternalRep {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)
    (g : X → G) (V : Set X) : Prop :=
  ∃ u : X → L, P.IsInternalRepOn g V u

variable {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)

theorem IsInternalRepOn.continuousOn {g : X → G} {V : Set X} {u : X → L}
    (h : P.IsInternalRepOn g V u) : ContinuousOn u V := h.1

theorem IsInternalRepOn.proj_eq {g : X → G} {V : Set X} {u : X → L}
    (h : P.IsInternalRepOn g V u) {x : X} (hx : x ∈ V) : P.proj (u x) = g x := h.2 x hx

/-- **DERIVED.**  A representative on a set is a representative on every subset. -/
theorem IsInternalRepOn.mono {g : X → G} {V V' : Set X} {u : X → L}
    (h : P.IsInternalRepOn g V u) (hsub : V' ⊆ V) : P.IsInternalRepOn g V' u :=
  ⟨h.1.mono hsub, fun x hx => h.2 x (hsub hx)⟩

/-- **DERIVED.**  Representatives pull back along continuous maps.  This is what lets a
representative on a double overlap be read on a triple overlap. -/
theorem IsInternalRepOn.comp {Y : Type w} [TopologicalSpace Y] {g : X → G} {V : Set X}
    {u : X → L} (h : P.IsInternalRepOn g V u) {f : Y → X} (hf : Continuous f) :
    P.IsInternalRepOn (fun y => g (f y)) (f ⁻¹' V) (fun y => u (f y)) :=
  ⟨h.1.comp hf.continuousOn fun _ hy => hy, fun y hy => h.2 (f y) hy⟩

theorem HasContinuousInternalRep.mono {g : X → G} {V V' : Set X}
    (h : P.HasContinuousInternalRep g V) (hsub : V' ⊆ V) :
    P.HasContinuousInternalRep g V' :=
  let ⟨u, hu⟩ := h; ⟨u, hu.mono P hsub⟩

/-- **PACKAGE C (item 32), principal — HARD TARGET A.**  Local continuous representability:
every point of the domain of a continuous ordinary map has an open neighbourhood carrying a
continuous internal representative.  The representative is obtained by composing `g` with an
inherited continuous local section of the projection; no pointwise selection is made. -/
theorem exists_local_continuous_internal_rep {g : X → G} (hg : Continuous g) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ P.HasContinuousInternalRep g V := by
  obtain ⟨W, hWopen, hxW, s, hs, hsec⟩ := P.hasLocalSection (g x)
  refine ⟨g ⁻¹' W, hWopen.preimage hg, hxW, fun y => s (g y), ?_, ?_⟩
  · exact hs.comp hg.continuousOn fun y hy => hy
  · intro y hy
    exact hsec (g y) hy

/-- **PACKAGE C.**  The same statement in neighbourhood form. -/
theorem exists_internal_rep_nhds {g : X → G} (hg : Continuous g) (x : X) :
    ∃ V ∈ nhds x, P.HasContinuousInternalRep g V := by
  obtain ⟨V, hV, hxV, hrep⟩ := P.exists_local_continuous_internal_rep hg x
  exact ⟨V, hV.mem_nhds hxV, hrep⟩

/-- **PACKAGE L (items 90, 94).**  Local existence holds everywhere; whole-domain existence
is *not* asserted. -/
theorem hasContinuousInternalRep_locally {g : X → G} (hg : Continuous g) :
    ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ P.HasContinuousInternalRep g V :=
  fun x => P.exists_local_continuous_internal_rep hg x

/-! ## Package D — refinement of the overlap cover (items 35–40) -/

/-- **NEWLY DEFINED (item 35), principal.**  A neutral refinement of the domain of an
ordinary map: an auxiliary index type, open subdomains covering the domain, and a continuous
internal representative stored on each of them (item 37).  A representative over the whole
domain is deliberately *not* part of the data (items 38, 39). -/
structure OverlapRefinement {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)
    (g : X → G) where
  /-- The auxiliary refinement index. -/
  Idx : Type w
  /-- The refined open subdomains. -/
  V : Idx → Set X
  /-- Each refined subdomain is open. -/
  isOpen_V : ∀ a, IsOpen (V a)
  /-- The refined subdomains cover the domain. -/
  covers : ∀ x : X, ∃ a, x ∈ V a
  /-- The stored continuous internal representative on each refined subdomain. -/
  rep : Idx → (X → L)
  /-- Each stored map is a continuous internal representative there. -/
  rep_isRep : ∀ a, P.IsInternalRepOn g (V a) (rep a)

namespace OverlapRefinement

variable {P} {g : X → G}

theorem continuousOn_rep (R : P.OverlapRefinement g) (a : R.Idx) :
    ContinuousOn (R.rep a) (R.V a) := (R.rep_isRep a).1

theorem proj_rep (R : P.OverlapRefinement g) (a : R.Idx) {x : X} (hx : x ∈ R.V a) :
    P.proj (R.rep a x) = g x := (R.rep_isRep a).2 x hx

/-- **DERIVED (item 34).**  Every point of the domain lies in a refined subdomain carrying a
continuous internal representative. -/
theorem exists_mem_with_rep (R : P.OverlapRefinement g) (x : X) :
    ∃ a : R.Idx, x ∈ R.V a ∧ P.HasContinuousInternalRep g (R.V a) := by
  obtain ⟨a, ha⟩ := R.covers x
  exact ⟨a, ha, ⟨R.rep a, R.rep_isRep a⟩⟩

end OverlapRefinement

/-- **PACKAGE D (item 36), principal.**  The refinement exists: from local continuous
representability one constructs a refinement of the domain carrying continuous internal
representatives.  The index type is the domain itself — the minimal dependent index of
neighbourhoods, no general refinement library. -/
noncomputable def refinementOfContinuous {g : X → G} (hg : Continuous g) :
    P.OverlapRefinement g := by
  choose V hVopen hxV hrep using fun x => P.exists_local_continuous_internal_rep hg x
  choose u hu using hrep
  exact
    { Idx := X
      V := V
      isOpen_V := hVopen
      covers := fun x => ⟨x, hxV x⟩
      rep := u
      rep_isRep := hu }

/-- **PACKAGE D (item 40).**  If a representative over the whole domain happens to exist, it
is a special case: it induces the one-element refinement. -/
noncomputable def OverlapRefinement.ofGlobal {g : X → G} {u : X → L}
    (hu : P.IsInternalRepOn g Set.univ u) : P.OverlapRefinement g where
  Idx := PUnit.{w + 1}
  V := fun _ => Set.univ
  isOpen_V := fun _ => isOpen_univ
  covers := fun _ => ⟨PUnit.unit, Set.mem_univ _⟩
  rep := fun _ => u
  rep_isRep := fun _ => hu

/-! ## Package L — whole-domain representability is an additional condition (items 91–94) -/

/-- **PACKAGE L (items 91, 94).**  The exact logical status of whole-domain representability:
it *implies* representability on every subset, and it is implied by nothing proved here.  A
concrete refutation, for the native circle double cover, is in the controls
(`SpineControls.circleDoubleCover_no_whole_domain_rep`). -/
theorem hasContinuousInternalRep_univ_imp {g : X → G} (h : P.HasContinuousInternalRep g Set.univ)
    (V : Set X) : P.HasContinuousInternalRep g V :=
  h.mono P (Set.subset_univ V)

end InternalProjection

end NullSectorTask28
