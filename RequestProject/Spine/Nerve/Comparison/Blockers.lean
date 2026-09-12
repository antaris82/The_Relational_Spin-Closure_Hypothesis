import RequestProject.Spine.Nerve.Comparison.RelativeMap

/-!
# Task 14, WP19 : the blockers, stated as Lean propositions

Task 14 ends **negatively on the topological side**.  This module states, in Lean and not only
in prose, the exact propositions that are missing.  Nothing here is assumed anywhere: these are
`Prop`-valued definitions, they are used only as explicit hypotheses, and no `axiom`, `sorry`
or `native_decide` occurs in the project.

The three blockers, in dependency order:

* **B2 `RealizationInjective`** (in `Task14Comparison`) — geometric realization of a
  monomorphism of simplicial sets is injective.  Needed for the relative singular *pair*
  sequence of the realized skeletal pair to exist at all.
* **B1 `StandardCellPairAcyclic` / `StandardCellPairTop`** — the homology of the standard cell
  pair `(|Δ[r]|,|∂Δ[r]|;ℤ₂)`: zero away from degree `r`, one-dimensional in degree `r`.
* **B3 `RelJIsIso`** — the relative comparison `J^rel` is an isomorphism on homology.  This is
  the WP11/WP12 target; classically it follows from B1 by excision plus additivity over the
  cells.

`Task14Comparison.oneSkeletonStep` proves, unconditionally in the pinned environment, that

`B2  ∧  (J is a homology iso on K^{(r-1)})  ∧  B3  ⟹  J is a homology iso on K^{(r)}`.

So the whole of Task 14 reduces to B1, B2, B3, and nothing else.  See
`TASK14_SPECIALIZED_CELL_ATTACHMENT.md` for the dependency DAG, the route audit and the
recommended Task 15.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13

universe u

namespace SpineTask14

/-! The pair `(|Δ[r]|, |∂Δ[r]|)` itself, `SpineTask14.stdCellPair`, and the blocker-B1
propositions about its relative homology, are standard-cell statements and live in
`RequestProject.Spine.Nerve.StandardCell.Pair`. -/

/-- **Blocker B3.**  The canonical relative comparison of WP12 is an isomorphism on homology in
every degree.  Classically this follows from B1 by excision (or by the quotient/wedge route)
plus additivity over the attached cells; neither ingredient exists in the pin. -/
def RelJIsIso (X : SSet.{u}) (r : ℕ) : Prop :=
  ∀ q, IsIso (HomologicalComplex.homologyMap (relJ X r) q)

/-- **The Task-14 reduction, in one statement.**  Given the two topological blockers `B2` and
`B3` for the step `r`, and the comparison already known on the `(r-1)`-skeleton, the comparison
holds on the `r`-skeleton.  This is `oneSkeletonStep` repackaged so that the remaining
dependencies are visible as named propositions. -/
theorem oneSkeletonStep_of_blockers (X : SSet.{u}) (r : ℕ)
    (hB2 : RealizationInjective X r)
    (h₁ : ∀ q, IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X r))) q))
    (hB3 : RelJIsIso X r) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X (r + 1)))) q) :=
  oneSkeletonStep X r hB2 h₁ hB3 q

end SpineTask14
