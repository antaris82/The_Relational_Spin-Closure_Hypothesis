import RequestProject.Spine.GoodCover.GoodCover
import RequestProject.Spine.GoodCover.PointCohomology

/-!
# Task 7, WP3 (b) : acyclic covers, kept strictly apart from good covers

WP3 insists that *good* and *acyclic* not be conflated.  This module defines the acyclic
condition in the only form that is meaningful inside this project — with respect to the
**native Task-5 singular mod-2 cohomology** — and records exactly how the two notions are
related here.

`GoodCoverZ2.IsAcyclicCover U` asks that every finite overlap be

* preconnected (the degree-zero condition, in the form the Čech bridge consumes), and
* cohomologically trivial in every positive degree, `Hᵏ⁺¹_sing(overlap;ℤ₂) = 0`.

## Good versus acyclic in this project

* Both notions imply the Task-6 constancy conditions, because both contain (respectively
  imply) preconnectedness of the overlaps — see `RequestProject.Spine.GoodCover.Constancy`.
* `IsGoodCover → IsAcyclicCover` is **not proved here** and is not assumed: contractibility of
  an overlap gives a homotopy equivalence with a point, and turning that into an isomorphism
  of the Task-5 cohomology groups is precisely the missing homotopy-invariance theorem (WP9).
  The *coefficient half* of that implication is available and proved
  (`Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`: the cohomology of a point
  vanishes above degree zero); only the transport along a homotopy equivalence is missing.
* Neither notion is claimed to imply the other in the reverse direction.

`isAcyclicCover_of_subsingleton` shows the definition is satisfiable.
-/

noncomputable section

namespace GoodCoverZ2

open CechZ2 Mod2Cohomology

universe w t

variable {X : Type w} [TopologicalSpace X] {ι : Type t}

/-- **The acyclic-cover predicate** (with respect to the native Task-5 singular mod-2
cohomology): an open cover whose finite overlaps are preconnected and have vanishing
cohomology in all positive degrees. -/
structure IsAcyclicCover (U : ι → Set X) : Prop where
  /-- Every member of the cover is open. -/
  isOpen : ∀ i, IsOpen (U i)
  /-- The family covers the space. -/
  covers : ∀ x : X, ∃ i, x ∈ U i
  /-- Degree-zero condition, in the form the Čech bridge consumes. -/
  preconnected_inter : ∀ {n : ℕ} (σ : Fin (n + 1) → ι), IsPreconnected (inter U σ)
  /-- Positive-degree vanishing on the *nonempty* overlaps (the only ones the nerve sees). -/
  acyclic_inter : ∀ {n : ℕ} (σ : Fin (n + 1) → ι), (inter U σ).Nonempty → ∀ (k : ℕ)
    (q : Cohomology (TopCat.of (inter U σ)) (k + 1)), q = 0

namespace IsAcyclicCover

variable {U : ι → Set X} (h : IsAcyclicCover U)
include h

/-- Double overlaps of an acyclic cover are preconnected. -/
theorem isPreconnected_pair (i j : ι) : IsPreconnected (U i ∩ U j) := by
  rw [← inter_pair' U i j]
  exact h.preconnected_inter _

/-- Triple overlaps of an acyclic cover are preconnected. -/
theorem isPreconnected_triple (i j k : ι) : IsPreconnected (U i ∩ U j ∩ U k) := by
  rw [← inter_triple' U i j k]
  exact h.preconnected_inter _

end IsAcyclicCover

/-- The predicate is satisfiable: on a space with at most one point, the one-element cover is
acyclic (its overlaps are the whole space, whose positive-degree cohomology vanishes by
`Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`). -/
theorem isAcyclicCover_of_subsingleton [Subsingleton X] [Nonempty X] :
    IsAcyclicCover (fun _ : PUnit.{t + 1} => (Set.univ : Set X)) := by
  refine ⟨fun _ => isOpen_univ, fun x => ⟨PUnit.unit, Set.mem_univ x⟩, ?_, ?_⟩
  · intro n σ
    exact Set.Subsingleton.isPreconnected (Set.subsingleton_of_subsingleton)
  · intro n σ _ k q
    have huniv : inter (fun _ : PUnit.{t + 1} => (Set.univ : Set X)) σ = Set.univ := by
      ext x; simp [inter]
    revert q
    rw [huniv]
    intro q
    haveI : Subsingleton (TopCat.of (Set.univ : Set X)) := Set.univ.subsingleton_coe.mpr
      Set.subsingleton_of_subsingleton
    haveI : Nonempty (TopCat.of (Set.univ : Set X)) :=
      ⟨⟨Classical.arbitrary X, Set.mem_univ _⟩⟩
    exact cohomology_succ_eq_zero_of_subsingleton k q

end GoodCoverZ2
