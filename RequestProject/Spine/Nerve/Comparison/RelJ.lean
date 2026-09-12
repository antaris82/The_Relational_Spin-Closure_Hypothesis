import RequestProject.Spine.Nerve.CellFamily.TargetDecomposition
import RequestProject.Spine.Nerve.Comparison.FiniteCriterion

/-!
# Blocker B3 : the frozen comparison `relJ` is an isomorphism on relative homology

The high-level join of the Stage-1.3 development.  Three independently developed branches meet
here and nowhere earlier:

* the **source** decomposition of the simplicial skeletal pair and the componentwise
  compatibility of the frozen comparison `relJ`
  (`RequestProject.Spine.Nerve.Comparison.SourceDecomposition`,
  `RequestProject.Spine.Nerve.Comparison.FamilyCompatibility`);
* the **single standard cell** comparison `cellRelJ`
  (`RequestProject.Spine.Nerve.StandardCell.RelativeComparison`);
* the **target** decomposition for the cell family
  (`RequestProject.Spine.Nerve.CellFamily.TargetDecomposition`).

The cell family `X.nonDegenerate r` is arbitrary: no finiteness hypothesis is used, the
direct-sum homology decomposition being available for an arbitrary index type
(`RequestProject.Spine.AlgebraicTopology.DirectSumHomology`).  The finite-family forms are
retained as wrappers.

No geometry, homological-algebra or standard-cell module may import this one.
-/

noncomputable section

open CategoryTheory Limits Simplicial SSet NerveGeom SpineTask14 SpineTask22 SpineTask23

universe u

namespace SpineTask24

variable (X : SSet.{u}) (r : ℕ)

/-- **The singular cell-family decomposition**, for an arbitrary family of `r`-cells. -/
theorem singularCellFamilyAdditivity : SingularCellFamilyAdditivity X r :=
  fun q => isIso_tgtDecomp X r q

/-- **Blocker B3.**  The frozen comparison `relJ X r` is an isomorphism on relative homology in
every degree, for an arbitrary simplicial set: the source decomposition and the single-cell
comparison are isomorphisms, and so is the target decomposition. -/
theorem relJIsIso : SpineTask14.RelJIsIso X r :=
  relJIsIso_of_singularCellFamilyAdditivity X r (singularCellFamilyAdditivity X r)

/-! ## The finite-family forms, retained for compatibility -/

/-- The singular cell-family decomposition for a finite family of `r`-cells. -/
theorem singularCellFamilyAdditivity_finite [Fintype ↑(X.nonDegenerate r)] :
    SingularCellFamilyAdditivity X r :=
  singularCellFamilyAdditivity X r

/-- The same statement in the finite-family form. -/
theorem finiteSingularCellFamilyAdditivity_finite [Fintype ↑(X.nonDegenerate r)] :
    FiniteSingularCellFamilyAdditivity X r :=
  fun q => isIso_tgtDecomp X r q

/-- The finite-family case of blocker B3. -/
theorem relJIsIso_finite [Fintype ↑(X.nonDegenerate r)] : SpineTask14.RelJIsIso X r :=
  relJIsIso X r

end SpineTask24
