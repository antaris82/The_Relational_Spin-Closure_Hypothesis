import RequestProject.Spine.Emergent.Symmetric
import RequestProject.Spine.E2.Cech.Cover

/-!
# Spine / Emergent : the adapter from the emergent base to the Čech-cover interface

**Explicit adapter module (Task 32, §15).**  The base-independent modules
`Emergent.LocalModel`, `Emergent.BaseGluing`, `Emergent.Reconstruction` and
`Emergent.Symmetric` do *not* import any cover-over-`X` machinery.  This module — and only
this module — connects the two: it exhibits the chart images of an emergent base as an
object of the existing cover interface `CechSpinLift.CechCover`, so that the Spin-side layers
can be run over an emergent base instead of an externally supplied one.

Nothing is re-proved here: `EmergentBase.emergentCover` is built from
`BaseGluingData.isOpen_chartRange` and `BaseGluingData.iUnion_chartRange`.

The adapter also records two facts about the *symmetric* sector, which are what the Spin
uniqueness gate consumes:

* every member of the emergent cover of the neutral sector is the whole base
  (`EmergentBase.symmetricCover_U_eq_univ`), hence all overlaps are the whole base;
* consequently its double overlaps are preconnected as soon as the local domain is.

The nerve-level (Čech) consequences are drawn in the comparison layer, which is the only
place where the emergent base and the Čech/Spin machinery are seen together.
-/

noncomputable section

namespace EmergentBase

open CechSpinLift BaseGluingData

universe u v t

variable {V : Type u} [TopologicalSpace V] {ι : Type t}

/-- **NEWLY DEFINED (Task 32), the adapter.**  The emergent cover of an emergent base: its
members are the chart images of the local pieces. -/
def emergentCover (B : BaseGluingData V ι) : CechCover (Space B) ι where
  U := B.chartRange
  isOpen_U := B.isOpen_chartRange
  covers p := by
    have : p ∈ (⋃ i, B.chartRange i) := by rw [B.iUnion_chartRange]; trivial
    simpa using this

@[simp] theorem emergentCover_U (B : BaseGluingData V ι) (i : ι) :
    (emergentCover B).U i = B.chartRange i := rfl

/-- **NEWLY DEFINED (Task 32).**  The trivial (identically `1`) transition cocycle on a
cover.  It exists on *every* cover, which is exactly why fibre data cannot see the base. -/
def trivialCocycle (G : Type v) [Group G] [TopologicalSpace G] {X : Type u} [TopologicalSpace X]
    {ι : Type t} (𝓤 : CechCover X ι) : VisibleCocycle G 𝓤 where
  g _ _ _ := 1
  continuousOn_g _ _ := continuousOn_const
  cocycle _ _ _ _ _ := one_mul 1

@[simp] theorem trivialCocycle_g {G : Type v} [Group G] [TopologicalSpace G] {X : Type u}
    [TopologicalSpace X] {κ : Type t} {𝓤 : CechCover X κ} (i j : κ) (x : X) :
    (trivialCocycle G 𝓤).g i j x = 1 := rfl

/-! ## The emergent cover of the symmetric sector -/

variable {D : Set V} (hD : IsOpen D)

@[simp] theorem symmetricCover_U_eq_univ (i : ι) :
    (emergentCover (symmetricGluing ι hD)).U i = Set.univ :=
  symmetricGluing.chartRange_eq_univ hD i

theorem symmetricCover_overlap₂_eq_univ (i j : ι) :
    (emergentCover (symmetricGluing ι hD)).overlap₂ i j = Set.univ := by
  rw [CechCover.overlap₂, emergentCover_U, emergentCover_U,
    symmetricGluing.chartRange_eq_univ hD i, symmetricGluing.chartRange_eq_univ hD j,
    Set.inter_univ]

/-- **DERIVED (Task 32).**  The double overlaps of the emergent cover of the neutral sector
are preconnected as soon as the local domain is. -/
theorem symmetricCover_isPreconnected_overlap₂ {κ : Type t} [Nonempty κ] {D : Set V}
    (hD : IsOpen D) (hconn : IsPreconnected D) (i j : κ) :
    IsPreconnected ((emergentCover (symmetricGluing κ hD)).overlap₂ i j) := by
  haveI : PreconnectedSpace (Space (symmetricGluing κ hD)) :=
    symmetricGluing.preconnectedSpace hD hconn
  rw [symmetricCover_overlap₂_eq_univ hD i j]
  exact isPreconnected_univ

end EmergentBase

end
