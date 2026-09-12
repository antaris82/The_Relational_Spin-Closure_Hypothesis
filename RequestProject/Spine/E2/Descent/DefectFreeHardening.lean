import RequestProject.Spine.E2.Descent.Inherited

/-!
# Task 29, Package B: repeated-index normalization from a vanishing triple defect

**HARD TARGET A, first half (items 23–29).**

The Task-XXVIII defect is used exactly as inherited,

`δ_ijk = (u_jk * u_ij) * u_ik⁻¹`,

and *no* normalization is assumed of the stored representatives.  Assuming only that all
reconstructed triple defects are trivial (the inherited predicate
`IsCompatibleInternalTransitionSystem`, re-exposed here as `TripleDefectFree`), we specialize
the triple law to repeated indices and derive, on the common domain where the relevant
representatives are simultaneously defined:

* `u_ii = 1` — from `δ_iii = (u_ii * u_ii) * u_ii⁻¹` (item 25);
* `u_ji = u_ij⁻¹` — from the repeated-index triple `(i, j, i)` together with `u_ii = 1`
  (item 26);
* the exact internal triple law `u_jk * u_ij = u_ik` (item 27).

The three are packaged as
`defectFree_implies_normalized_transition_laws_on_common_domain` (item 28).

Nothing here concludes that representatives living on *different* refinement patches agree:
that is the separate question of Package C/D (item 29).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

/-! ## Repeated-index algebra of the inherited defect -/

section RawAlgebra

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type u} [TopologicalSpace X]

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **DERIVED (item 25).**  The inherited defect on a completely repeated index triple is the
representative itself: `δ_iii = (u * u) * u⁻¹ = u`. -/
theorem tripleDefect_repeated (u : X → L) (x : X) : tripleDefect u u u x = u x := by
  simp [tripleDefect]

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE B (item 25).**  Identity normalization, raw form: a trivial completely repeated
defect forces the representative to be the internal unit. -/
theorem eq_one_of_tripleDefect_repeated {u : X → L} {x : X} (h : tripleDefect u u u x = 1) :
    u x = 1 := by
  rw [tripleDefect_repeated] at h; exact h

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE B (item 26).**  Inverse normalization, raw form: if the `(i,j,i)` defect is
trivial and the diagonal representative is the unit, the two representatives of the two
directions are inverse to each other. -/
theorem inv_of_tripleDefect_repeated {uij uji uii : X → L} {x : X}
    (h : tripleDefect uij uji uii x = 1) (h1 : uii x = 1) : uji x = (uij x)⁻¹ := by
  rw [tripleDefect_apply, h1, inv_one, mul_one] at h
  exact eq_inv_of_mul_eq_one_left h

end RawAlgebra

/-! ## Lifting a point of a double overlap to a repeated-index triple overlap -/

section Lifts

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] (S : TransitionSystem B ι G)

/-- The point of `U i ∩ U i` under a point of `U i ∩ U j`. -/
def diagPt {i j : ι} (x : ↥(S.U i ∩ S.U j)) : ↥(S.U i ∩ S.U i) := ⟨(x : B), x.2.1, x.2.1⟩

/-- The same point of the overlap, read in the opposite order. -/
def swapPt {i j : ι} (x : ↥(S.U i ∩ S.U j)) : ↥(S.U j ∩ S.U i) := ⟨(x : B), x.2.2, x.2.1⟩

/-- A point of `U i ∩ U i`, read on the triple overlap `(i,i,i)`. -/
def liftIII {i : ι} (y : ↥(S.U i ∩ S.U i)) : ↥(S.tripleDom i i i) :=
  ⟨(y : B), ⟨y.2.1, y.2.2⟩, y.2.2⟩

/-- A point of `U i ∩ U j`, read on the triple overlap `(i,i,j)`. -/
def liftIIJ {i j : ι} (x : ↥(S.U i ∩ S.U j)) : ↥(S.tripleDom i i j) :=
  ⟨(x : B), ⟨x.2.1, x.2.1⟩, x.2.2⟩

/-- A point of `U i ∩ U j`, read on the triple overlap `(i,j,i)`. -/
def liftIJI {i j : ι} (x : ↥(S.U i ∩ S.U j)) : ↥(S.tripleDom i j i) :=
  ⟨(x : B), ⟨x.2.1, x.2.2⟩, x.2.1⟩

variable {S}

@[simp] theorem incIJ_liftIII {i : ι} (y : ↥(S.U i ∩ S.U i)) :
    S.incIJ i i i (liftIII S y) = y := rfl

@[simp] theorem incJK_liftIII {i : ι} (y : ↥(S.U i ∩ S.U i)) :
    S.incJK i i i (liftIII S y) = y := rfl

@[simp] theorem incIK_liftIII {i : ι} (y : ↥(S.U i ∩ S.U i)) :
    S.incIK i i i (liftIII S y) = y := rfl

@[simp] theorem incIJ_liftIIJ {i j : ι} (x : ↥(S.U i ∩ S.U j)) :
    S.incIJ i i j (liftIIJ S x) = diagPt S x := rfl

@[simp] theorem incJK_liftIIJ {i j : ι} (x : ↥(S.U i ∩ S.U j)) :
    S.incJK i i j (liftIIJ S x) = x := rfl

@[simp] theorem incIK_liftIIJ {i j : ι} (x : ↥(S.U i ∩ S.U j)) :
    S.incIK i i j (liftIIJ S x) = x := rfl

@[simp] theorem incIJ_liftIJI {i j : ι} (x : ↥(S.U i ∩ S.U j)) :
    S.incIJ i j i (liftIJI S x) = x := rfl

@[simp] theorem incJK_liftIJI {i j : ι} (x : ↥(S.U i ∩ S.U j)) :
    S.incJK i j i (liftIJI S x) = swapPt S x := rfl

@[simp] theorem incIK_liftIJI {i j : ι} (x : ↥(S.U i ∩ S.U j)) :
    S.incIK i j i (liftIJI S x) = diagPt S x := rfl

end Lifts

/-! ## The defect-free predicate -/

section DefectFree

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-- **NEWLY DEFINED (item 35), name for the inherited predicate.**  A refined internal
candidate is *triple-defect free* when every reconstructed Task-XXVIII triple defect is
trivial, for **all** index triples — including repeated ones — and all refinement patches on
which it is defined.  This is literally the inherited
`IsCompatibleInternalTransitionSystem`; the Task-XXIX name only records its rôle. -/
def TripleDefectFree (C : InternalTransitionCandidate P S) : Prop :=
  IsCompatibleInternalTransitionSystem C

theorem TripleDefectFree.defect_eq_one {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k)
    {x : ↥(S.tripleDom i j k)} (hx : x ∈ C.defectDom i j k a b c) :
    C.defect i j k a b c x = 1 := h i j k a b c x hx

/-- **PACKAGE B (item 25), principal endpoint.**  *Defect-free implies identity
normalization.*  On every refinement patch of a diagonal overlap the stored representative is
the internal unit. -/
theorem defectFree_identity_normalisation {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) (i : ι) (a : C.Idx i i) {y : ↥(S.U i ∩ S.U i)}
    (hy : y ∈ C.V i i a) : C.u i i a y = 1 := by
  have hx : liftIII S y ∈ C.defectDom i i i a a a := ⟨⟨hy, hy⟩, hy⟩
  have hd := h.defect_eq_one i i i a a a hx
  have hval : C.defect i i i a a a (liftIII S y)
      = tripleDefect (fun _ : ↥(S.tripleDom i i i) => C.u i i a y)
          (fun _ => C.u i i a y) (fun _ => C.u i i a y) (liftIII S y) := rfl
  rw [hval] at hd
  exact eq_one_of_tripleDefect_repeated hd

/-- **PACKAGE B (item 26), principal endpoint.**  *Defect-free implies inverse
normalization.*  The stored representative of the `(j,i)` transition is the inverse of the
stored representative of the `(i,j)` transition, wherever the two — and some diagonal patch —
are simultaneously defined. -/
theorem defectFree_inverse_normalisation {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) (i j : ι) (a : C.Idx i j) (b : C.Idx j i) (c : C.Idx i i)
    {x : ↥(S.U i ∩ S.U j)} (ha : x ∈ C.V i j a) (hb : swapPt S x ∈ C.V j i b)
    (hc : diagPt S x ∈ C.V i i c) :
    C.u j i b (swapPt S x) = (C.u i j a x)⁻¹ := by
  have hx : liftIJI S x ∈ C.defectDom i j i a b c := ⟨⟨ha, hb⟩, hc⟩
  have hd := h.defect_eq_one i j i a b c hx
  have hval : C.defect i j i a b c (liftIJI S x)
      = tripleDefect (fun _ : ↥(S.tripleDom i j i) => C.u i j a x)
          (fun _ => C.u j i b (swapPt S x)) (fun _ => C.u i i c (diagPt S x))
          (liftIJI S x) := rfl
  rw [hval] at hd
  exact inv_of_tripleDefect_repeated hd (defectFree_identity_normalisation h i c hc)

/-- **PACKAGE B (item 27), principal endpoint.**  *Defect-free implies the exact internal
triple law* `u_jk * u_ij = u_ik` on every common domain of three stored representatives.
This is the inherited equivalence `exact_compatibility_iff_defect_trivial`, applied to the
defect-free hypothesis. -/
theorem defectFree_exact_triple_law {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k)
    {x : ↥(S.tripleDom i j k)} (hx : x ∈ C.defectDom i j k a b c) :
    C.u j k b (S.incJK i j k x) * C.u i j a (S.incIJ i j k x)
      = C.u i k c (S.incIK i j k x) :=
  (C.exact_compatibility_iff_defect_trivial i j k a b c).2 (h i j k a b c) x hx

/-- **PACKAGE B (item 28), principal endpoint — the packaged strongest correct result.**
`defectFree_implies_normalized_transition_laws_on_common_domain`: on the common domains where
the relevant stored representatives are simultaneously defined, a triple-defect-free refined
candidate satisfies exactly the three normalization laws of an internal transition system:
identity, inverse, and the exact triple-overlap multiplication law.

It does **not** assert that representatives living on different refinement patches of the
same overlap agree (item 29); that is settled separately in `PairwiseDescent`. -/
theorem defectFree_implies_normalized_transition_laws_on_common_domain
    {C : InternalTransitionCandidate P S} (h : TripleDefectFree C) :
    (∀ (i : ι) (a : C.Idx i i) (y : ↥(S.U i ∩ S.U i)), y ∈ C.V i i a → C.u i i a y = 1) ∧
      (∀ (i j : ι) (a : C.Idx i j) (b : C.Idx j i) (c : C.Idx i i) (x : ↥(S.U i ∩ S.U j)),
        x ∈ C.V i j a → swapPt S x ∈ C.V j i b → diagPt S x ∈ C.V i i c →
          C.u j i b (swapPt S x) = (C.u i j a x)⁻¹) ∧
      (∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k)
          (x : ↥(S.tripleDom i j k)), x ∈ C.defectDom i j k a b c →
        C.u j k b (S.incJK i j k x) * C.u i j a (S.incIJ i j k x)
          = C.u i k c (S.incIK i j k x)) :=
  ⟨fun i a _ hy => defectFree_identity_normalisation h i a hy,
    fun i j a b c _ ha hb hc => defectFree_inverse_normalisation h i j a b c ha hb hc,
    fun i j k a b c _ hx => defectFree_exact_triple_law h i j k a b c hx⟩

end DefectFree

end NullSectorTask29
