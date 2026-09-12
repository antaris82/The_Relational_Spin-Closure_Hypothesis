import RequestProject.Spine.Nerve.Comparison.BaseCase
import RequestProject.Spine.Nerve.Geometry.PointModel

/-!
# The skeletal comparison with the geometric blocker discharged

This is the join of two branches that are independent up to this point:

* the **geometry** of the realized standard cell
  (`RequestProject.Spine.Nerve.Geometry.PointModel`), which supplies
  `SpineTask16.standardCellMono`, i.e. blocker `B2` for the standard cell;
* the **canonical comparison** (`RequestProject.Spine.Nerve.Comparison.BaseCase`), which
  carries the one-skeleton step, the skeletal induction and the finite-dimensional
  comparison theorem, each still conditional on the standard-cell statement.

Feeding the former into the latter removes the hypothesis `StandardCellMono` everywhere.
Nothing new is proved here: every declaration is a literal application.  The results used to
live next to the point-model geometry; they are comparison statements, so they belong here.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SpineTask16

/-- The realization blocker `B2`, in the shape Task 14 consumes. -/
theorem realizationInjective (K : SSet.{u}) (r : ℕ) : SpineTask14.RealizationInjective K r :=
  SpineTask15.realizationInjective_of_standardCellMono K r (standardCellMono r)

/-- **The Task-14 one-skeleton step, with the realization blocker removed.** -/
theorem oneSkeletonStep (K : SSet.{u}) (r : ℕ)
    (h₁ : ∀ q, IsIso (HomologicalComplex.homologyMap
      (SpineTask14.sSetChainComplexFunctor.map (sSetTopAdj.unit.app (SpineTask13.Sk K r))) q))
    (hB3 : SpineTask14.RelJIsIso K r) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (SpineTask14.sSetChainComplexFunctor.map
        (sSetTopAdj.unit.app (SpineTask13.Sk K (r + 1)))) q) :=
  SpineTask15.oneSkeletonStep_of_standardCell K r (standardCellMono r) h₁ hB3 q

/-- The Task-15 skeletal induction, with the standard-cell hypothesis discharged: only the
relative comparison hypothesis `RelJIsIso` remains. -/
theorem skeletalInduction (K : SSet.{u}) (hrel : ∀ r, SpineTask14.RelJIsIso K r) :
    ∀ (r q : ℕ), IsIso (HomologicalComplex.homologyMap
      (SpineTask14.sSetChainComplexFunctor.map (sSetTopAdj.unit.app (SpineTask13.Sk K r))) q) :=
  SpineTask15.skeletalInduction K standardCellMono hrel

/-- The Task-15 finite-dimensional comparison theorem, with the standard-cell hypothesis
discharged: only the relative comparison hypothesis `RelJIsIso` remains. -/
theorem finiteDimensional_homologyIso (K : SSet.{u}) (d : ℕ) [K.HasDimensionLT d]
    (hrel : ∀ r, SpineTask14.RelJIsIso K r) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (SpineTask14.sSetChainComplexFunctor.map (sSetTopAdj.unit.app K)) q) :=
  SpineTask15.finiteDimensional_homologyIso K d standardCellMono hrel q

end SpineTask16
