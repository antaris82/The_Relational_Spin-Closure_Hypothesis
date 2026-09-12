import RequestProject.Spine.E2.Lift.RepresentativeChange

/-!
# Task 3, WP2 : abstract Čech covers and the visible transition cocycle

This is the first module of the Task-3 layer.  It works over a completely abstract
topological base `X`: **no manifold, no tangent bundle, no frame bundle, no metric** is
present, and none is constructible from the data below.

Two objects are introduced.

* `CechSpinLift.CechCover X ι` — an indexed family of open sets covering `X`.  This is the
  *cover representation* of the Task-3 layer.  It is deliberately lighter than the inherited
  `NullSectorTask27.OrdinaryTransitionSystem` of the E2 spine, which bundles a cover
  *together with* transition maps into one fixed visible model group; here the cover is a
  separate object so that a refinement map `𝓥 → 𝓤` (WP9) can be formulated.

* `CechSpinLift.VisibleCocycle G 𝓤` — `G`-valued transition data on `𝓤`, continuous on each
  double overlap and satisfying the **exact** Čech 1-cocycle law
  `g i j x * g j k x = g i k x` on every triple overlap.

The normalisations `g i i = 1` and `g j i = (g i j)⁻¹` are *not* assumed: they are derived
from the cocycle law (`VisibleCocycle.g_self`, `VisibleCocycle.g_symm`), as WP2 demands.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace CechSpinLift

universe u v w t

/-! ## The cover representation -/

/-- **NEWLY DEFINED (WP2), principal.**  An open cover of an abstract topological space,
indexed by an arbitrary type.  No further structure on `X` is assumed. -/
structure CechCover (X : Type w) [TopologicalSpace X] (ι : Type t) where
  /-- The chart domains. -/
  U : ι → Set X
  /-- Each chart domain is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- The chart domains cover the base. -/
  covers : ∀ x : X, ∃ i, x ∈ U i

namespace CechCover

variable {X : Type w} [TopologicalSpace X] {ι : Type t}

/-- The double overlap `U i ∩ U j`. -/
def overlap₂ (𝓤 : CechCover X ι) (i j : ι) : Set X := 𝓤.U i ∩ 𝓤.U j

/-- The triple overlap `U i ∩ U j ∩ U k`. -/
def overlap₃ (𝓤 : CechCover X ι) (i j k : ι) : Set X := 𝓤.U i ∩ 𝓤.U j ∩ 𝓤.U k

/-- The quadruple overlap `U i ∩ U j ∩ U k ∩ U l`. -/
def overlap₄ (𝓤 : CechCover X ι) (i j k l : ι) : Set X :=
  𝓤.U i ∩ 𝓤.U j ∩ 𝓤.U k ∩ 𝓤.U l

@[simp] theorem mem_overlap₂ (𝓤 : CechCover X ι) (i j : ι) (x : X) :
    x ∈ 𝓤.overlap₂ i j ↔ x ∈ 𝓤.U i ∧ x ∈ 𝓤.U j := Iff.rfl

@[simp] theorem mem_overlap₃ (𝓤 : CechCover X ι) (i j k : ι) (x : X) :
    x ∈ 𝓤.overlap₃ i j k ↔ (x ∈ 𝓤.U i ∧ x ∈ 𝓤.U j) ∧ x ∈ 𝓤.U k := Iff.rfl

@[simp] theorem mem_overlap₄ (𝓤 : CechCover X ι) (i j k l : ι) (x : X) :
    x ∈ 𝓤.overlap₄ i j k l ↔ ((x ∈ 𝓤.U i ∧ x ∈ 𝓤.U j) ∧ x ∈ 𝓤.U k) ∧ x ∈ 𝓤.U l := Iff.rfl

theorem isOpen_overlap₂ (𝓤 : CechCover X ι) (i j : ι) : IsOpen (𝓤.overlap₂ i j) :=
  (𝓤.isOpen_U i).inter (𝓤.isOpen_U j)

theorem isOpen_overlap₃ (𝓤 : CechCover X ι) (i j k : ι) : IsOpen (𝓤.overlap₃ i j k) :=
  ((𝓤.isOpen_U i).inter (𝓤.isOpen_U j)).inter (𝓤.isOpen_U k)

theorem isOpen_overlap₄ (𝓤 : CechCover X ι) (i j k l : ι) : IsOpen (𝓤.overlap₄ i j k l) :=
  (((𝓤.isOpen_U i).inter (𝓤.isOpen_U j)).inter (𝓤.isOpen_U k)).inter (𝓤.isOpen_U l)

/-! ### The inclusions between overlaps, used everywhere downstream -/

theorem overlap₃_subset_ij (𝓤 : CechCover X ι) (i j k : ι) :
    𝓤.overlap₃ i j k ⊆ 𝓤.overlap₂ i j := fun _ hx => ⟨hx.1.1, hx.1.2⟩

theorem overlap₃_subset_jk (𝓤 : CechCover X ι) (i j k : ι) :
    𝓤.overlap₃ i j k ⊆ 𝓤.overlap₂ j k := fun _ hx => ⟨hx.1.2, hx.2⟩

theorem overlap₃_subset_ik (𝓤 : CechCover X ι) (i j k : ι) :
    𝓤.overlap₃ i j k ⊆ 𝓤.overlap₂ i k := fun _ hx => ⟨hx.1.1, hx.2⟩

theorem overlap₄_subset_ijk (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.overlap₃ i j k := fun _ hx => hx.1

theorem overlap₄_subset_ijl (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.overlap₃ i j l := fun _ hx => ⟨hx.1.1, hx.2⟩

theorem overlap₄_subset_ikl (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.overlap₃ i k l := fun _ hx => ⟨⟨hx.1.1.1, hx.1.2⟩, hx.2⟩

theorem overlap₄_subset_jkl (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.overlap₃ j k l := fun _ hx => ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩

theorem overlap₄_subset_U₁ (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.U i := fun _ hx => hx.1.1.1

theorem overlap₄_subset_U₂ (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.U j := fun _ hx => hx.1.1.2

theorem overlap₄_subset_U₃ (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.U k := fun _ hx => hx.1.2

theorem overlap₄_subset_U₄ (𝓤 : CechCover X ι) (i j k l : ι) :
    𝓤.overlap₄ i j k l ⊆ 𝓤.U l := fun _ hx => hx.2

end CechCover

/-! ## The visible transition cocycle -/

/-- **NEWLY DEFINED (WP2), principal.**  Visible `G`-valued transition data on a cover:
one map per ordered pair of indices, continuous on the double overlap, satisfying the exact
Čech 1-cocycle law on every triple overlap.

Only the cocycle law is assumed; the unit and inverse normalisations are theorems below. -/
structure VisibleCocycle (G : Type v) [Group G] [TopologicalSpace G] {X : Type w}
    [TopologicalSpace X] {ι : Type t} (𝓤 : CechCover X ι) where
  /-- The visible transition functions. -/
  g : ι → ι → (X → G)
  /-- Each transition function is continuous on its double overlap. -/
  continuousOn_g : ∀ i j, ContinuousOn (g i j) (𝓤.overlap₂ i j)
  /-- The exact Čech 1-cocycle law on triple overlaps. -/
  cocycle : ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, g i j x * g j k x = g i k x

namespace VisibleCocycle

variable {G : Type v} [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X]
  {ι : Type t} {𝓤 : CechCover X ι}

/-- **DERIVED (WP2).**  The diagonal transition is the unit: taking `i = j = k` in the
cocycle law gives `g i i x * g i i x = g i i x`. -/
theorem g_self (T : VisibleCocycle G 𝓤) (i : ι) {x : X} (hx : x ∈ 𝓤.U i) : T.g i i x = 1 := by
  have h := T.cocycle i i i x ⟨⟨hx, hx⟩, hx⟩
  have h2 : T.g i i x * T.g i i x = 1 * T.g i i x := by rw [one_mul]; exact h
  exact mul_right_cancel h2

/-- **DERIVED (WP2).**  The transposed transition is the inverse: taking `k = i` in the
cocycle law and using `g i i = 1`. -/
theorem g_symm (T : VisibleCocycle G 𝓤) (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) :
    T.g j i x = (T.g i j x)⁻¹ := by
  have h := T.cocycle i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩
  rw [T.g_self i hx.1] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **DERIVED (WP2).**  The cocycle law rewritten in the order used by the inherited
triple-defect machinery: `g i k = g i j * g j k`. -/
theorem cocycle' (T : VisibleCocycle G 𝓤) (i j k : ι) {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) :
    T.g i k x = T.g i j x * T.g j k x := (T.cocycle i j k x hx).symm

/-- **WP2, packaged endpoint.**  The visible transition data satisfies the three exact
compatibility conditions demanded by WP2: the unit law, the inverse law and the triple
overlap cocycle law.  Only the last is assumed; the first two are derived. -/
theorem visible_transition_laws (T : VisibleCocycle G 𝓤) :
    (∀ i, ∀ x ∈ 𝓤.U i, T.g i i x = 1) ∧
    (∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, T.g j i x = (T.g i j x)⁻¹) ∧
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, T.g i j x * T.g j k x = T.g i k x) :=
  ⟨fun i _ hx => T.g_self i hx, fun i j _ hx => T.g_symm i j hx, T.cocycle⟩

end VisibleCocycle

/-! ## Cover refinement and the pullback of visible transition data (WP9, first half) -/

/-- **NEWLY DEFINED (WP9), principal.**  A refinement map of covers: an index map `r` and
the inclusion `V a ⊆ U (r a)`.  This is the only notion of refinement used in Task 3. -/
structure CoverRefinement {X : Type w} [TopologicalSpace X] {ι' : Type t} {ι : Type t}
    (𝓥 : CechCover X ι') (𝓤 : CechCover X ι) where
  /-- The index map of the refinement. -/
  r : ι' → ι
  /-- Each refined patch sits inside the patch of the image index. -/
  le : ∀ a, 𝓥.U a ⊆ 𝓤.U (r a)

namespace CoverRefinement

variable {X : Type w} [TopologicalSpace X] {ι ι' : Type t} {𝓥 : CechCover X ι'}
  {𝓤 : CechCover X ι}

theorem overlap₂_le (R : CoverRefinement 𝓥 𝓤) (a b : ι') :
    𝓥.overlap₂ a b ⊆ 𝓤.overlap₂ (R.r a) (R.r b) :=
  fun _ hx => ⟨R.le a hx.1, R.le b hx.2⟩

theorem overlap₃_le (R : CoverRefinement 𝓥 𝓤) (a b c : ι') :
    𝓥.overlap₃ a b c ⊆ 𝓤.overlap₃ (R.r a) (R.r b) (R.r c) :=
  fun _ hx => ⟨⟨R.le a hx.1.1, R.le b hx.1.2⟩, R.le c hx.2⟩

theorem overlap₄_le (R : CoverRefinement 𝓥 𝓤) (a b c d : ι') :
    𝓥.overlap₄ a b c d ⊆ 𝓤.overlap₄ (R.r a) (R.r b) (R.r c) (R.r d) :=
  fun _ hx => ⟨⟨⟨R.le a hx.1.1.1, R.le b hx.1.1.2⟩, R.le c hx.1.2⟩, R.le d hx.2⟩

/-- **NEWLY DEFINED (WP9), principal.**  The pullback of visible transition data along a
refinement: `g^𝓥_{ab} := g_{r a, r b}`.  Continuity and the exact cocycle law are inherited,
not re-assumed. -/
def pullback {G : Type v} [Group G] [TopologicalSpace G] (R : CoverRefinement 𝓥 𝓤)
    (T : VisibleCocycle G 𝓤) : VisibleCocycle G 𝓥 where
  g a b := T.g (R.r a) (R.r b)
  continuousOn_g a b := (T.continuousOn_g _ _).mono (R.overlap₂_le a b)
  cocycle a b c x hx := T.cocycle _ _ _ x (R.overlap₃_le a b c hx)

@[simp] theorem pullback_g {G : Type v} [Group G] [TopologicalSpace G]
    (R : CoverRefinement 𝓥 𝓤) (T : VisibleCocycle G 𝓤) (a b : ι') :
    (R.pullback T).g a b = T.g (R.r a) (R.r b) := rfl

/-- The identity refinement of a cover by itself. -/
def id (𝓤 : CechCover X ι) : CoverRefinement 𝓤 𝓤 where
  r := _root_.id
  le _ := subset_rfl

/-- Composition of refinement maps. -/
def comp {ι'' : Type t} {𝓦 : CechCover X ι''} (R' : CoverRefinement 𝓦 𝓥)
    (R : CoverRefinement 𝓥 𝓤) : CoverRefinement 𝓦 𝓤 where
  r := R.r ∘ R'.r
  le a := (R'.le a).trans (R.le (R'.r a))

@[simp] theorem comp_r {ι'' : Type t} {𝓦 : CechCover X ι''} (R' : CoverRefinement 𝓦 𝓥)
    (R : CoverRefinement 𝓥 𝓤) (a : ι'') : (R'.comp R).r a = R.r (R'.r a) := rfl

end CoverRefinement

end CechSpinLift
