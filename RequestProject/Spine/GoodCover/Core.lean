import RequestProject.Spine.GoodCover.Presimplicial
import RequestProject.Spine.GoodCover.NerveIdentification
import RequestProject.Spine.GoodCover.GoodCover
import RequestProject.Spine.GoodCover.PointCohomology
import RequestProject.Spine.GoodCover.AcyclicCover
import RequestProject.Spine.GoodCover.ManifoldCovers
import RequestProject.Spine.GoodCover.Constancy
import RequestProject.Spine.GoodCover.SingularComparisonSpec
import RequestProject.Spine.GoodCover.W2Interface
import RequestProject.Spine.Cohomology.HomotopyInvariance
import RequestProject.Spine.GoodCover.GoodCoverAcyclic
import RequestProject.Spine.GoodCover.HardenedSpec

/-!
# Spine / GoodCover / Core : the Task-7 endpoint

Task 7 asks whether the smooth-manifold setting of Task 4 supplies covers for which the
fixed-cover Čech class of Task 6 can be compared with the singular cohomology of Task 5.  The
honest answer, in the pinned library, is: **the cover-side questions close, the comparison
does not**, and the missing theorems are named precisely.

## What is proved (unconditional)

* **WP3** — the good-cover predicate `GoodCoverZ2.IsGoodCover` and the exact implication chain
  `contractible ⇒ path connected ⇒ connected ⇒ preconnected`, with the strictness control
  `contractible_ne_preconnected`; hence
  `GoodCoverZ2.goodCover_constOn`: **a good cover makes the Task-6 constancy conditions
  automatic**, and the whole Task-6 Spin package becomes unconditional
  (`spinLiftCechClassGood`, its lift-independence, and
  `frameCechClassGood_eq_zero_iff_spinStructure`).
* **WP3(b)** — acyclic covers (`GoodCoverZ2.IsAcyclicCover`) are defined separately, with
  respect to the native Task-5 cohomology, and are *not* identified with good covers.
* **WP5** — the nerve of a cover is exhibited as a presimplicial set
  (`NerveZ2.coverNerve`) whose simplicial `ℤ₂` cochain complex is built independently
  (`NerveZ2.Presimplicial`, with its own `δ² = 0`), and the Task-6 Čech complex **is** that
  complex: `NerveZ2.coverNerve_cohomology`, `NerveZ2.cechCohomologyEquiv` (the identity).
* **WP2/WP4** — the Task-4 manifold class (charted on the four-dimensional carrier) is
  strongly locally contractible, has arbitrarily fine **contractible open** neighbourhoods,
  and admits a cover by contractible open sets refining any given cover
  (`SpineTop.exists_contractible_open_nhds`, `SpineTop.exists_contractible_refinement`,
  `LorentzFrames.contractibleCover`).  Good-cover *existence* is **not** proved: Outcome C.
* **WP9 (partial)** — the native mod-2 cohomology of a one-point space vanishes above degree
  zero (`Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`), proved directly.
* **WP13** — on a good cover the canonical map into the older Task-3 obstruction carrier is
  injective (`GoodCoverZ2.toObstruction_injective_of_goodCover`).

## What is conditional, and on exactly what

`RequestProject.Spine.GoodCover.SingularComparisonSpec` names the three missing theorems as
hypothesis structures — homotopy invariance (WP9), the nerve theorem (WP6), the
simplicial-to-singular comparison (WP8) — and proves everything downstream of them:
`GoodCoverSpec.Comparison.equiv` (WP10), `GoodCoverSpec.spinLiftSingularClass` (WP11) with
lift-independence and
`GoodCoverSpec.frameSingularClass_eq_zero_iff_spinStructure`, and the refinement invariance
`GoodCoverSpec.spinLiftSingularClass_refinement` (WP12).  Cover independence in full needs, in
addition, common good refinements (`GoodCoverSpec.CommonGoodRefinement`).

None of these hypotheses is an axiom, none is a typeclass, and nothing in the production Spine
consumes them.

## What is deliberately not done

`w₂(TM)` is **not** defined, and the Spin obstruction is **not** called `w₂`.
`RequestProject.Spine.GoodCover.W2Interface` fixes only the interface an independent future
construction must satisfy, and the statement to be proved about it.

The class `[z]` remains a purely topological Spin-lift obstruction: not curvature, torsion, a
spin connection, a gauge field strength, a synchronization mismatch, gravity, matter, mass,
dynamics or confinement.
-/

/-! ## Axiom audit of the principal Task-7 declarations -/

#print axioms NerveZ2.Presimplicial.coboundary_coboundary
#print axioms NerveZ2.Presimplicial.Cohomology
#print axioms NerveZ2.coverNerve
#print axioms NerveZ2.coverNerve_cohomology
#print axioms NerveZ2.cechCohomologyEquiv
#print axioms GoodCoverZ2.IsGoodCover
#print axioms GoodCoverZ2.contractible_ne_preconnected
#print axioms GoodCoverZ2.IsGoodCover.isPreconnected_inter
#print axioms GoodCoverZ2.IsAcyclicCover
#print axioms GoodCoverZ2.isAcyclicCover_of_subsingleton
#print axioms GoodCoverZ2.goodCover_constOn
#print axioms GoodCoverZ2.spinLiftCechClassGood
#print axioms GoodCoverZ2.spinLiftCechClassGood_lift_independent
#print axioms GoodCoverZ2.spinLiftCechClassGood_eq_zero_iff
#print axioms GoodCoverZ2.frameCechClassGood_eq_zero_iff_spinStructure
#print axioms GoodCoverZ2.toObstruction_injective_of_goodCover
#print axioms Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton
#print axioms SpineTop.stronglyLocallyContractibleSpace_of_normed
#print axioms SpineTop.exists_contractible_open_nhds
#print axioms SpineTop.stronglyLocallyContractibleSpace_of_chartedSpace
#print axioms SpineTop.exists_contractible_refinement
#print axioms SpineTop.HasGoodCover
#print axioms SpineTop.hasGoodCover_of_contractible
#print axioms LorentzFrames.contractibleCover
#print axioms LorentzFrames.contractibleCover_contractible
#print axioms GoodCoverSpec.HomotopyInvariance.cohomology_succ_eq_zero_of_contractible
#print axioms GoodCoverSpec.isAcyclicCover_of_isGoodCover
#print axioms GoodCoverSpec.Comparison.equiv
#print axioms GoodCoverSpec.Comparison.equiv_eq_zero_iff
#print axioms GoodCoverSpec.spinLiftSingularClass
#print axioms GoodCoverSpec.spinLiftSingularClass_lift_independent
#print axioms GoodCoverSpec.spinLiftSingularClass_eq_zero_iff
#print axioms GoodCoverSpec.frameSingularClass_eq_zero_iff_spinStructure
#print axioms GoodCoverSpec.spinLiftSingularClass_refinement
#print axioms GoodCoverSpec.spinLiftSingularClass_common_refinement
#print axioms GoodCoverSpec.spinStructure_iff_of_agrees
