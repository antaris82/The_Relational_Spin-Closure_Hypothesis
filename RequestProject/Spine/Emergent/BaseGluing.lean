import RequestProject.Spine.Emergent.LocalModel

/-!
# Spine / Emergent : the explicit base-gluing primitive

**Second module of the manifold-emergence layer (Task 32, §7 "base-gluing gate").**

## Why a new primitive is introduced here

The certified Spin data of the project have the form

`g̃_ij : U i ∩ U j → L`   (`SpinNative.NativeSpinTransitionData`),

and their projections `ρ ∘ g̃_ij : U i ∩ U j → G`.  Both are functions *defined on subsets of
an already given base* and valued in the internal/visible group.  Their content is: given a
point which is already known to lie in two chart domains, how the two fibre coordinates over
it are compared.  Nothing in that datum mentions

* which points the local pieces consist of,
* which local points of two different pieces are the same point,
* what the local coordinate domains are, or
* the topology of the result.

Consequently *fibre gluing is not base gluing*, and no attempt is made here to read a
transition function `g̃_ij` as a coordinate change.  The negative statement is proved in
`RequestProject.Spine.Emergent.NonDerivability`: two base-gluing data carrying literally the
same (trivial) Spin transition data have non-homeomorphic emergent bases.

`BaseGluingData` below is therefore **an explicit sufficient base-gluing primitive**, and it
is exposed in full: local domains, an overlap relation, the base-point identification maps,
and the compatibility laws.

**Exact strength of the claim (corrected in Task 33).**  What is *proved* about this
primitive is (i) that it suffices — the reconstruction of
`RequestProject.Spine.Emergent.Reconstruction` builds a base out of it — and (ii) that its
cross-piece incidence layer is irreducibly additional: the indexed local pieces alone do not
determine the base
(`RequestProject.Spine.Emergent.LocalPieceData.base_incidence_not_determined_by_local_piece_data`).
It is **not** proved, and it is not claimed here, that every individual field of
`BaseGluingData` is separately necessary, nor that this structure is the unique minimal
presentation of the missing information.  The earlier phrase "the minimal missing primitive"
overstated the theorems and has been replaced.  It is not hidden behind an opaque "emergence" wrapper, and it contains
no metric, connection, transport, holonomy or curvature.

## The datum

For a topological local model `V` (in the intended instantiation
`V = EmergentBase.LocalModel`, the four-dimensional Clifford/Lorentz model) and an index type
`ι`:

* `D i ⊆ V` — the open local domain of piece `i`;
* `W i j ⊆ D i` — the open part of piece `i` which is identified with a part of piece `j`
  (the *incidence* datum: `W i j = ∅` means the pieces `i` and `j` do not meet);
* `φ i j : V → V` — the base-point identification, mapping `W i j` into `W j i`;
* the laws `W i i = D i`, `φ i i = id` on `D i`, `φ j i ∘ φ i j = id` on `W i j`, and the
  cocycle law on triple incidences.

These are exactly the atlas-level coherence conditions demanded by Task 32 §7 Case 1
(`φ_ii = id`, `φ_ji = φ_ij⁻¹`, `φ_jk ∘ φ_ij = φ_ik`), here as the *definition* of the
primitive rather than as a derived property of Spin data — because they are not derivable
from Spin data.
-/

namespace EmergentBase

universe u t

/-- **NEWLY DEFINED (Task 32), an explicit sufficient base-gluing primitive.**  Local
domains in a topological local model `V`, an incidence relation between them, base-point
identification maps and their compatibility laws.

Its cross-piece incidence layer is information that the Spin/Lorentz fibre data provably do
*not* contain (Task 32/33); no minimality or uniqueness of the presentation is claimed. -/
structure BaseGluingData (V : Type u) [TopologicalSpace V] (ι : Type t) where
  /-- The local domain of the piece `i`. -/
  D : ι → Set V
  /-- Local domains are open in the local model. -/
  isOpen_D : ∀ i, IsOpen (D i)
  /-- The incidence datum: the part of piece `i` identified with part of piece `j`. -/
  W : ι → ι → Set V
  /-- Incidence domains are open. -/
  isOpen_W : ∀ i j, IsOpen (W i j)
  /-- Incidence domains sit inside their own local domain. -/
  W_subset : ∀ i j, W i j ⊆ D i
  /-- A piece is incident to itself along all of it. -/
  W_self : ∀ i, W i i = D i
  /-- The base-point identification maps. -/
  φ : ι → ι → V → V
  /-- The identifications are continuous where defined. -/
  continuousOn_φ : ∀ i j, ContinuousOn (φ i j) (W i j)
  /-- They map the `i`-side of the incidence onto the `j`-side. -/
  φ_mapsTo : ∀ i j, Set.MapsTo (φ i j) (W i j) (W j i)
  /-- `φ_ii = id`. -/
  φ_self : ∀ i, ∀ x ∈ D i, φ i i x = x
  /-- `φ_ji = φ_ij⁻¹`. -/
  φ_inv : ∀ i j, ∀ x ∈ W i j, φ j i (φ i j x) = x
  /-- The cocycle law: if `x` is `i`-incident to `j` and its `j`-image is `j`-incident to
  `k`, then `x` is `i`-incident to `k` and the identifications compose. -/
  φ_cocycle : ∀ i j k, ∀ x ∈ W i j, φ i j x ∈ W j k → x ∈ W i k ∧ φ j k (φ i j x) = φ i k x

namespace BaseGluingData

variable {V : Type u} [TopologicalSpace V] {ι : Type t} (B : BaseGluingData V ι)

/-! ## The atlas-level coherence laws, in the packaged form of Task 32 §7 -/

/-- **DERIVED.**  `φ_ij` maps the `j`-side back to the `i`-side. -/
theorem φ_mapsTo_symm (i j : ι) : Set.MapsTo (B.φ j i) (B.W j i) (B.W i j) :=
  B.φ_mapsTo j i

/-- **DERIVED.**  `φ_ij` is a bijection of `W i j` onto `W j i`, with inverse `φ_ji`. -/
theorem φ_leftInverse (i j : ι) : Set.LeftInvOn (B.φ j i) (B.φ i j) (B.W i j) :=
  fun _ hx => B.φ_inv i j _ hx

theorem φ_rightInverse (i j : ι) : Set.RightInvOn (B.φ j i) (B.φ i j) (B.W j i) :=
  fun _ hy => B.φ_inv j i _ hy

theorem φ_bijOn (i j : ι) : Set.BijOn (B.φ i j) (B.W i j) (B.W j i) :=
  Set.BijOn.mk (B.φ_mapsTo i j) ((B.φ_leftInverse i j).injOn)
    (fun y hy => ⟨B.φ j i y, B.φ_mapsTo j i hy, B.φ_inv j i y hy⟩)

/-- **DERIVED, the packaged atlas coherence of Task 32 §7.**  The base transition maps
satisfy the identity, inverse and composition laws on their domains. -/
theorem atlas_coherence :
    (∀ i, ∀ x ∈ B.D i, B.φ i i x = x) ∧
    (∀ i j, Set.BijOn (B.φ i j) (B.W i j) (B.W j i)) ∧
    (∀ i j, ∀ x ∈ B.W i j, B.φ j i (B.φ i j x) = x) ∧
    (∀ i j k, ∀ x ∈ B.W i j, B.φ i j x ∈ B.W j k →
      x ∈ B.W i k ∧ B.φ j k (B.φ i j x) = B.φ i k x) :=
  ⟨B.φ_self, B.φ_bijOn, fun i j _ hx => B.φ_inv i j _ hx, B.φ_cocycle⟩

/-- **DERIVED.**  `φ_ij` is an open map from `W i j` onto the open set `W j i`: it is a
homeomorphism of the incidence domains, so images of open sets are open in `V`. -/
theorem isOpen_image_φ (i j : ι) {S : Set V} (hS : IsOpen S) :
    IsOpen (B.φ i j '' (B.W i j ∩ S)) := by
  have himg : B.φ i j '' (B.W i j ∩ S) = B.W j i ∩ B.φ j i ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxW, hxS⟩, rfl⟩
      exact ⟨B.φ_mapsTo i j hxW, by simpa [B.φ_inv i j x hxW] using hxS⟩
    · rintro ⟨hyW, hyS⟩
      exact ⟨B.φ j i y, ⟨B.φ_mapsTo j i hyW, hyS⟩, B.φ_inv j i y hyW⟩
  rw [himg]
  exact (B.continuousOn_φ j i).isOpen_inter_preimage (B.isOpen_W j i) hS

/-! ## The tagged local carrier and the gluing relation -/

/-- **NEWLY DEFINED (Task 32).**  The tagged disjoint union of the local pieces,
`X₀ = ⨿ i, D i`.  No identification has been made yet. -/
def Total (B : BaseGluingData V ι) : Type _ := Σ i : ι, (B.D i : Set V)

instance : TopologicalSpace (Total B) := inferInstanceAs (TopologicalSpace (Σ i, (B.D i : Set V)))

/-- The gluing relation on the tagged carrier: `(i, x)` and `(j, y)` describe the same base
point exactly when `x` is `i`-incident to `j` and `φ_ij x = y`. -/
def Rel (B : BaseGluingData V ι) (p q : Total B) : Prop :=
  (p.2 : V) ∈ B.W p.1 q.1 ∧ B.φ p.1 q.1 (p.2 : V) = (q.2 : V)

theorem rel_refl (p : Total B) : B.Rel p p := by
  refine ⟨?_, B.φ_self p.1 _ p.2.2⟩
  rw [B.W_self p.1]; exact p.2.2

theorem rel_symm {p q : Total B} (h : B.Rel p q) : B.Rel q p := by
  obtain ⟨hW, hφ⟩ := h
  refine ⟨?_, ?_⟩
  · exact hφ ▸ B.φ_mapsTo p.1 q.1 hW
  · rw [← hφ, B.φ_inv p.1 q.1 _ hW]

theorem rel_trans {p q r : Total B} (h₁ : B.Rel p q) (h₂ : B.Rel q r) : B.Rel p r := by
  obtain ⟨hW₁, hφ₁⟩ := h₁
  obtain ⟨hW₂, hφ₂⟩ := h₂
  have hmem : B.φ p.1 q.1 (p.2 : V) ∈ B.W q.1 r.1 := by rw [hφ₁]; exact hW₂
  obtain ⟨hik, hcomp⟩ := B.φ_cocycle p.1 q.1 r.1 _ hW₁ hmem
  refine ⟨hik, ?_⟩
  rw [← hcomp, hφ₁, hφ₂]

/-- **DERIVED (Task 32).**  The gluing relation of a base-gluing datum is an equivalence
relation; no relation has to be *generated*, because the primitive's own laws are exactly
reflexivity, symmetry and transitivity. -/
def setoid (B : BaseGluingData V ι) : Setoid (Total B) where
  r := B.Rel
  iseqv := ⟨B.rel_refl, B.rel_symm, B.rel_trans⟩

theorem setoid_iff {p q : Total B} : (B.setoid).r p q ↔ B.Rel p q := Iff.rfl

/-- **DERIVED.**  Two points of the *same* piece are identified only if they are equal. -/
theorem rel_same_index {i : ι} {x y : (B.D i : Set V)}
    (h : B.Rel ⟨i, x⟩ ⟨i, y⟩) : x = y :=
  Subtype.ext (by rw [← h.2, B.φ_self i _ x.2])

end BaseGluingData

end EmergentBase
