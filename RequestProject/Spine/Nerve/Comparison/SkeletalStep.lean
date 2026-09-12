import RequestProject.Spine.Nerve.Comparison.Blockers
import RequestProject.Spine.Nerve.Skeleton.RealizationMono

/-!
# The one-skeleton step with the geometric blocker discharged

The join of two independent branches:

* the **geometry** of the realized skeletal inclusion
  (`RequestProject.Spine.Nerve.Skeleton.RealizationMono`): the realization of the skeletal
  inclusion is injective as soon as the realization of `∂Δ[r] ⟶ Δ[r]` is, `StandardCellMono r`;
* the **canonical comparison** (`RequestProject.Spine.Nerve.Comparison.RelativeMap`,
  `…Comparison.Blockers`): the one-skeleton step `oneSkeletonStep`, and the blocker
  propositions `RealizationInjective`, `RelJIsIso`.

Only the two theorems below need both, so the geometry module no longer mentions the
comparison at all.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet NerveGeom SpineTask13 SpineTask14

universe u

namespace SpineTask15

variable (X : SSet.{u}) (r : ℕ)

/-- **WP3, in the form Task 14 consumes.**  The standard-cell statement implies the Task-14
hypothesis `RealizationInjective`, which is exactly what `oneSkeletonStep` carries. -/
theorem realizationInjective_of_standardCellMono (h : StandardCellMono.{u} r) :
    RealizationInjective X r := by
  have hinj := realization_skInc_injective X r h
  have hm : Mono (SSet.toTop.map (skInc X r)) := (TopCat.mono_iff_injective _).2 hinj
  intro n a b hab
  have hd : a.down ≫ SSet.toTop.map (skInc X r) = b.down ≫ SSet.toTop.map (skInc X r) :=
    congrArg ULift.down hab
  exact ULift.ext _ _ ((cancel_mono _).1 hd)


/-- **The Task-14 one-skeleton step, with blocker `B2` replaced by the standard-cell
statement.**  Compared with `SpineTask14.oneSkeletonStep_of_blockers`, the hypothesis
`RealizationInjective X r` — a statement about the arbitrary simplicial set `X` — has been
replaced by `StandardCellMono r`, a statement about the standard cell alone. -/
theorem oneSkeletonStep_of_standardCell (hcell : StandardCellMono.{u} r)
    (h₁ : ∀ q, IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X r))) q))
    (hB3 : RelJIsIso X r) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X (r + 1)))) q) :=
  oneSkeletonStep X r (realizationInjective_of_standardCellMono X r hcell) h₁ hB3 q

/-- Consequently `|K^{(-1)}| → |K^{(0)}|` is injective for every simplicial set `K`
(unconditionally). -/
theorem realizationInjective_zero (K : SSet.{u}) : RealizationInjective K 0 :=
  realizationInjective_of_standardCellMono K 0 standardCellMono_zero

end SpineTask15
