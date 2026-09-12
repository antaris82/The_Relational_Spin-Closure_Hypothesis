import RequestProject.Spine.Emergent.Symmetric

/-!
# Spine / Emergent : genuine canonicity in the symmetric sector

**Eighth module of the manifold-emergence layer (Task 33, §6).**

Task 32 proved `EmergentBase.symmetric_emergent_base_unique`, namely

`Nonempty (Space (symmetricGluing ι hD) ≃ₜ Space (symmetricGluing ι' hD))`,

by *choosing* an index in each presentation.  A `Nonempty` of homeomorphisms is existence,
not canonicity.  This module replaces it by a distinguished, choice-independent
identification and proves the coherence laws which justify the word "canonical":

* `EmergentBase.symmetricGluing.coordinate` — the intrinsic quotient coordinate
  `Space (symmetricGluing ι hD) → D`, obtained by descent of the local coordinate of a
  representative along the gluing relation.  No index is chosen: the descent condition is
  discharged by the relation itself.
* `EmergentBase.symmetricGluing.coordinate_chart`,
  `EmergentBase.symmetricGluing.chart_coordinate` — it is a two-sided inverse of *every*
  chart insertion.
* `EmergentBase.symmetricGluing.chart_independent_of_index` — `chart i x = chart j x` for
  all indices `i, j`: the required choice-independence statement.
* `EmergentBase.symmetricGluing.baseHomeomorph` — the distinguished homeomorphism
  `Space (symmetricGluing ι hD) ≃ₜ D` whose underlying map *is* the intrinsic coordinate.
  Classical choice is used only to package the inverse, and
  `EmergentBase.symmetricGluing.baseHomeomorph_symm_apply` proves that the packaged inverse
  agrees with the chart of *every* index, so the result does not depend on that choice.
* `EmergentBase.symmetricCanonicalHomeomorph` and the coherence laws
  `symmetricCanonicalHomeomorph_refl`, `symmetricCanonicalHomeomorph_symm`,
  `symmetricCanonicalHomeomorph_trans` — the comparison of two presentations of the
  symmetric sector, with the identity/inverse/composition laws of a canonical family.

**What is still not claimed.**  The quotient carriers of two presentations are *not* equal,
and no such claim is made; canonicity is the coherent family of identifications above.
-/

noncomputable section

namespace EmergentBase

universe u t t' t''

open BaseGluingData

variable {V : Type u} [TopologicalSpace V]

namespace symmetricGluing

variable {D : Set V} (hD : IsOpen D)

/-! ## The intrinsic quotient coordinate -/

/-- **NEWLY DEFINED (Task 33), the intrinsic quotient coordinate.**  In the symmetric sector
all pieces are the same domain `D`, all incidence domains are `D` and all identification
maps are the identity; therefore the local coordinate of a representative descends to the
quotient.  No index is chosen. -/
def coordinate {ι : Type t} : Space (symmetricGluing ι hD) → (D : Set V) :=
  Quotient.lift (fun p : Total (symmetricGluing ι hD) => (⟨(p.2 : V), p.2.2⟩ : (D : Set V)))
    (fun _ _ h => Subtype.ext ((rel_iff hD).1 h))

@[simp] theorem coordinate_mk {ι : Type t} (p : Total (symmetricGluing ι hD)) :
    coordinate hD ((symmetricGluing ι hD).quotMk p) = ⟨(p.2 : V), p.2.2⟩ := rfl

theorem continuous_coordinate {ι : Type t} :
    Continuous (coordinate (ι := ι) hD) := by
  apply Continuous.quotient_lift
  exact continuous_sigma fun _ => continuous_id

/-- **DERIVED (Task 33).**  The intrinsic coordinate undoes every chart insertion. -/
@[simp] theorem coordinate_chart {ι : Type t} (i : ι) (x : (D : Set V)) :
    coordinate hD ((symmetricGluing ι hD).chart i x) = x := rfl

/-- **DERIVED (Task 33), the choice-independence statement.**  In the symmetric sector the
chart insertions of all indices coincide. -/
theorem chart_independent_of_index {ι : Type t} (i j : ι) (x : (D : Set V)) :
    (symmetricGluing ι hD).chart i x = (symmetricGluing ι hD).chart j x :=
  ((symmetricGluing ι hD).mk_eq_mk_iff).2 ((rel_iff hD).2 rfl)

/-- **DERIVED (Task 33).**  Every chart insertion undoes the intrinsic coordinate. -/
@[simp] theorem chart_coordinate {ι : Type t} (i : ι) (p : Space (symmetricGluing ι hD)) :
    (symmetricGluing ι hD).chart i (coordinate hD p) = p := by
  obtain ⟨q, rfl⟩ := (symmetricGluing ι hD).mk_surjective p
  exact chart_independent_of_index hD i q.1 _

/-! ## The distinguished homeomorphism -/

/-- **NEWLY DEFINED (Task 33), PRINCIPAL — the distinguished homeomorphism of the symmetric
sector.**  Its underlying map is the intrinsic quotient coordinate; the inverse is the chart
insertion, which by `chart_independent_of_index` does not depend on the index used to
package it. -/
def baseHomeomorph (ι : Type t) [Nonempty ι] {D : Set V} (hD : IsOpen D) :
    Space (symmetricGluing ι hD) ≃ₜ (D : Set V) where
  toFun := coordinate hD
  invFun := (symmetricGluing ι hD).chart (Classical.arbitrary ι)
  left_inv p := chart_coordinate hD _ p
  right_inv x := coordinate_chart hD _ x
  continuous_toFun := continuous_coordinate hD
  continuous_invFun := (symmetricGluing ι hD).continuous_chart _

@[simp] theorem baseHomeomorph_apply (ι : Type t) [Nonempty ι] (p : Space (symmetricGluing ι hD)) :
    baseHomeomorph ι hD p = coordinate hD p := rfl

/-- **DERIVED (Task 33), the choice-independence of the packaged inverse.**  The inverse of
the distinguished homeomorphism is the chart insertion of *every* index, not just of the
arbitrarily chosen one. -/
@[simp] theorem baseHomeomorph_symm_apply (ι : Type t) [Nonempty ι] (i : ι) (x : (D : Set V)) :
    (baseHomeomorph ι hD).symm x = (symmetricGluing ι hD).chart i x :=
  chart_independent_of_index hD _ i x

/-- **DERIVED (Task 33).**  The Task-32 index-dependent homeomorphism `D ≃ₜ Space` is the
inverse of the distinguished one, for every index. -/
theorem homeomorph_eq_baseHomeomorph_symm {ι : Type t} [Nonempty ι] (i : ι) :
    homeomorph hD i = (baseHomeomorph ι hD).symm :=
  Homeomorph.ext fun x => (baseHomeomorph_symm_apply hD ι i x).symm

end symmetricGluing

/-! ## The canonical comparison of two presentations -/

open symmetricGluing

/-- **NEWLY DEFINED (Task 33), PRINCIPAL — the canonical comparison homeomorphism.**  Two
presentations of the symmetric sector on the same local domain, with any two nonempty index
types, are identified through their intrinsic coordinates.  This is a *named map*, not a
`Nonempty` statement, and it involves no choice of index. -/
def symmetricCanonicalHomeomorph (ι : Type t) (κ : Type t') [Nonempty ι] [Nonempty κ]
    {D : Set V} (hD : IsOpen D) :
    Space (symmetricGluing ι hD) ≃ₜ Space (symmetricGluing κ hD) :=
  (baseHomeomorph ι hD).trans (baseHomeomorph κ hD).symm

@[simp] theorem symmetricCanonicalHomeomorph_apply (ι : Type t) (κ : Type t')
    [Nonempty ι] [Nonempty κ] {D : Set V} (hD : IsOpen D) (p : Space (symmetricGluing ι hD)) :
    symmetricCanonicalHomeomorph ι κ hD p = (baseHomeomorph κ hD).symm (coordinate hD p) := rfl

/-- **DERIVED (Task 33), coherence law 1.**  The canonical comparison of a presentation with
itself is the identity. -/
@[simp] theorem symmetricCanonicalHomeomorph_refl (ι : Type t) [Nonempty ι] {D : Set V}
    (hD : IsOpen D) :
    symmetricCanonicalHomeomorph ι ι hD = Homeomorph.refl (Space (symmetricGluing ι hD)) :=
  Homeomorph.ext fun p => (baseHomeomorph ι hD).symm_apply_apply p

/-- **DERIVED (Task 33), coherence law 2.**  The inverse of the canonical comparison is the
canonical comparison in the opposite direction. -/
@[simp] theorem symmetricCanonicalHomeomorph_symm (ι : Type t) (κ : Type t')
    [Nonempty ι] [Nonempty κ] {D : Set V} (hD : IsOpen D) :
    (symmetricCanonicalHomeomorph ι κ hD).symm = symmetricCanonicalHomeomorph κ ι hD :=
  Homeomorph.ext fun _ => rfl

/-- **DERIVED (Task 33), coherence law 3.**  The canonical comparisons compose. -/
@[simp] theorem symmetricCanonicalHomeomorph_trans (ι : Type t) (κ : Type t') (μ : Type t'')
    [Nonempty ι] [Nonempty κ] [Nonempty μ] {D : Set V} (hD : IsOpen D) :
    (symmetricCanonicalHomeomorph ι κ hD).trans (symmetricCanonicalHomeomorph κ μ hD)
      = symmetricCanonicalHomeomorph ι μ hD :=
  Homeomorph.ext fun _ =>
    congrArg (baseHomeomorph μ hD).symm ((baseHomeomorph κ hD).apply_symm_apply _)

/-- **DERIVED (Task 33), PRINCIPAL — the strengthened uniqueness statement of the symmetric
sector.**  Replaces the Task-32 `Nonempty`-statement `symmetric_emergent_base_unique`: the
identification is a named map, it is the intrinsic coordinate comparison, it does not depend
on any index, and the family satisfies the identity, inverse and composition laws. -/
theorem symmetric_emergent_base_canonical (ι : Type t) (κ : Type t') [Nonempty ι] [Nonempty κ]
    {D : Set V} (hD : IsOpen D) :
    (∀ (i j : ι) (x : (D : Set V)),
        (symmetricGluing ι hD).chart i x = (symmetricGluing ι hD).chart j x) ∧
    (∀ (i : ι) (x : (D : Set V)), coordinate hD ((symmetricGluing ι hD).chart i x) = x) ∧
    (∀ (i : ι) (p : Space (symmetricGluing ι hD)),
        (symmetricGluing ι hD).chart i (coordinate hD p) = p) ∧
    (∀ p, symmetricCanonicalHomeomorph ι κ hD p
        = (baseHomeomorph κ hD).symm (coordinate hD p)) ∧
    symmetricCanonicalHomeomorph ι ι hD = Homeomorph.refl _ ∧
    (symmetricCanonicalHomeomorph ι κ hD).symm = symmetricCanonicalHomeomorph κ ι hD :=
  ⟨chart_independent_of_index hD, coordinate_chart hD, chart_coordinate hD,
    fun _ => rfl, symmetricCanonicalHomeomorph_refl ι hD,
    symmetricCanonicalHomeomorph_symm ι κ hD⟩

end EmergentBase

end
