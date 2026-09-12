import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# Geometric realization preserves colimits

Two generic facts about the geometric realization of simplicial sets, with no reference to a
nerve, a skeleton or a cell:

* `SpineTask14.realizationPreservesColimits` — `SSet.toTop` is a left adjoint (`sSetTopAdj`),
  hence preserves all colimits.  The pinned Mathlib does not state this as an instance for the
  shapes needed here;
* `SpineTask14.toTop_isPushout` — consequently a pushout square of simplicial sets is carried
  to a pushout square of topological spaces.  Nothing is assumed about *which* squares are
  pushouts.

Both are used by the skeletal pushout layer and by the canonical relative comparison, which
are otherwise independent of each other.  The declarations keep their historical namespace.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

namespace SpineTask14

/-- Geometric realization is a left adjoint, hence preserves all colimits. -/
instance realizationPreservesColimits : PreservesColimitsOfSize.{u, u} SSet.toTop.{u} :=
  sSetTopAdj.leftAdjoint_preservesColimits

/-- **The statement actually needed.**  Geometric realization carries a pushout square of
simplicial sets to a pushout square of topological spaces. -/
theorem toTop_isPushout {W X Y Z : SSet.{u}} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : IsPushout f g h i) :
    IsPushout (SSet.toTop.map f) (SSet.toTop.map g) (SSet.toTop.map h) (SSet.toTop.map i) := by
  -- the shape `WalkingSpan` lives in the smallest universe, so the `{u, u}` instance above has
  -- to be shrunk explicitly once this module no longer inherits the ambient instances of the
  -- old, wider import closure
  haveI : PreservesColimitsOfSize.{0, 0} SSet.toTop.{u} :=
    preservesSmallestColimits_of_preservesColimits _
  exact sq.map SSet.toTop

end SpineTask14
