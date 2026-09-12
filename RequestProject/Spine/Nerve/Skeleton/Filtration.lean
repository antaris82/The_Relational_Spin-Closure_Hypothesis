import RequestProject.Spine.AlgebraicTopology.SimplicialSkeleton
import RequestProject.Spine.AlgebraicTopology.DirectedUnionColimit

/-!
# The skeletal filtration as a diagram, and its colimit

The skeleta `Sk K r` of a simplicial set `K` form an increasing family of subcomplexes whose
union is `K`.  This module packages that family as a functor on the poset `ℕ` and proves the
identification

`K = colim_r Sk K r`

as an honest colimit cocone in `SSet` (`skIsColimit`).  Colimits of simplicial sets are
computed dimensionwise, and in each dimension the statement is that the skeleta exhaust the
simplices: a `q`-simplex already lies in `Sk K (q+1)`.

Nothing here mentions realization, singular chains or homology.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13

universe u

namespace NerveSkeleton

variable (K : SSet.{u})

/-- The inclusion of the `r`-th skeleton into the whole simplicial set. -/
abbrev skIncl (r : ℕ) : Sk K r ⟶ K := (K.skeleton r).ι

/-- The skeletal filtration `r ↦ Sk K r` as a functor on the poset `ℕ`. -/
@[simps obj]
def skFunctor : ℕ ⥤ SSet.{u} where
  obj r := Sk K r
  map {_ _} h := SSet.Subcomplex.homOfLE (K.skeleton.monotone (leOfHom h))
  map_id _ := rfl
  map_comp _ _ := (SSet.Subcomplex.homOfLE_comp _ _).symm

@[simp]
theorem skFunctor_map_comp_skIncl {r s : ℕ} (h : r ≤ s) :
    (skFunctor K).map (homOfLE h) ≫ skIncl K s = skIncl K r := rfl

/-- The transition maps of the skeletal filtration in terms of the one-step inclusion. -/
theorem skFunctor_map_succ {a b : ℕ} (hab : a ≤ b) (h : a ≤ b + 1) :
    (skFunctor K).map (homOfLE h) = (skFunctor K).map (homOfLE hab) ≫ skInc K b := rfl

/-- The cocone of the skeleta over `K`. -/
@[simps]
def skCocone : Cocone (skFunctor K) where
  pt := K
  ι := { app := fun r => skIncl K r }

/-- Every simplex of `K` lies in a skeleton. -/
theorem exists_mem_skeleton (n : SimplexCategoryᵒᵖ) (a : K.obj n) :
    ∃ (r : ℕ) (x : (Sk K r).obj n), (skIncl K r).app n x = a := by
  obtain ⟨Δ⟩ := n
  induction Δ using SimplexCategory.rec with | _ k => ?_
  exact ⟨k + 1, ⟨a, K.mem_skeleton a (Nat.lt_succ_self k)⟩, rfl⟩

/-- **The skeleta exhaust `K`.**  `K` is the colimit of its skeleta. -/
def skIsColimit : IsColimit (skCocone K) := by
  refine evaluationJointlyReflectsColimits _ (fun n => ?_)
  refine SpineDirectedUnion.isColimitOfInjectiveJointlySurjective _ (fun r x y hxy => ?_)
    (fun a => exists_mem_skeleton K n a)
  exact Subtype.ext hxy

end NerveSkeleton
