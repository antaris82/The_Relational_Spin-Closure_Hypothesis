import RequestProject.Spine.Cohomology.CupDescent
import RequestProject.Spine.E2.Cech.Obstruction

/-!
# Task 5, WP8 : the exact type gap between the fixed-cover obstruction and `H²_sing`

The Task-3 obstruction lives in

`CechSpinLift.ObstructionClass P 𝓤 = Quot (Cohomologous P 𝓤)`,

a quotient of **kernel-valued 2-cochains on one fixed open cover** `𝓤` of the base, while the
carrier constructed in Task 5 is

`Mod2Cohomology.Cohomology (TopCat.of X) 2 = Z²/B²` of **singular** mod-2 cochains.

These are different types with different constructions, and **no map between them is
constructed, assumed or used anywhere in this project**.  In particular this module does *not*
assert

`ObstructionClass P 𝓤 ≃ H²_sing(X;ℤ₂)`,

and the Spine contains no such statement.

What this module *does* provide is the precise **specification of the missing bridge**, as an
ordinary structure whose fields are exactly the properties a future comparison theorem would
have to supply, plus the (cheap) transport theorem showing what such a datum would buy.  A
`ComparisonDatum` is an ordinary hypothesis, given as an explicit argument: nothing here is an
axiom, and nothing downstream consumes it.

To exhibit one, a future task must prove a genuine Čech-to-singular comparison theorem for the
cover `𝓤`; the standard route requires, at minimum, a refinement/nerve argument together with
a good-cover or paracompactness hypothesis.  Those are **not** available in the pinned library
and are **not** assumed here.  See `TASK05_AUDIT.md`, WP8.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type u} [TopologicalSpace X] {ι : Type t}

/-- **The specification of the missing Čech-to-singular comparison** on a fixed cover.

A `ComparisonDatum` packages exactly what a future comparison theorem would have to deliver in
order to turn the fixed-cover obstruction class into an element of genuine singular mod-2
cohomology:

* `compare` — a map from the fixed-cover obstruction classes to `H²(X;ℤ₂)`;
* `compare_trivial` — it sends the trivial class to `0`;
* `compare_injective_at_trivial` — it *detects* triviality (only the trivial class is sent to
  `0`).

The second and third fields are the exact content that makes the comparison usable: without
the third one, vanishing of the image would be strictly weaker than vanishing of the class.
Nothing in the Spine constructs such a datum; it is stated here only so that the remaining
dependency is unambiguous. -/
structure ComparisonDatum (P : InternalProjection L G) (𝓤 : CechCover X ι) where
  /-- The comparison map into genuine singular mod-2 cohomology. -/
  compare : ObstructionClass P 𝓤 → Cohomology (TopCat.of X) 2
  /-- The trivial fixed-cover class is sent to `0`. -/
  compare_trivial : compare (trivialClass P 𝓤) = 0
  /-- Only the trivial fixed-cover class is sent to `0`. -/
  compare_injective_at_trivial :
    ∀ c : ObstructionClass P 𝓤, compare c = 0 → c = trivialClass P 𝓤

variable {P : InternalProjection L G} {𝓤 : CechCover X ι} {T : VisibleCocycle G 𝓤}

/-- **What the bridge would buy (conditional theorem).**  *If* a comparison datum for the
fixed cover exists, then the singular mod-2 class attached to a family of local Spin lifts
vanishes exactly when coherent Spin-valued transition data exists.

This is an honest conditional statement: the comparison datum is an explicit hypothesis, and
the theorem is proved by transporting the Task-3 endpoint
`obstruction_eq_trivialClass_iff_exists_coherent` along it.  It is *not* evidence that such a
datum exists. -/
theorem comparison_vanishing_iff_exists_coherent (Ψ : ComparisonDatum P 𝓤)
    (D : SpinLiftFamily P T) :
    Ψ.compare D.obstruction = 0 ↔ ∃ D' : SpinLiftFamily P T, D'.IsCoherent := by
  constructor
  · intro h
    exact (D.obstruction_eq_trivialClass_iff_exists_coherent).1
      (Ψ.compare_injective_at_trivial _ h)
  · intro h
    rw [(D.obstruction_eq_trivialClass_iff_exists_coherent).2 h]
    exact Ψ.compare_trivial

/-- The image of the obstruction under a comparison datum does not depend on the chosen family
of local Spin lifts — an immediate consequence of the Task-3 invariance theorem. -/
theorem comparison_lift_independent (Ψ : ComparisonDatum P 𝓤) (D D' : SpinLiftFamily P T) :
    Ψ.compare D.obstruction = Ψ.compare D'.obstruction := by
  rw [D.obstruction_lift_independent D']

end Mod2Cohomology
