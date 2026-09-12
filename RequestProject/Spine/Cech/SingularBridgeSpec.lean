import RequestProject.Spine.Cech.SpinInstance
import RequestProject.Spine.Cohomology.Core

/-!
# Task 6, WP12 : the exact specification of the next bridge `Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)`

Task 5 could only specify a comparison **out of the custom Task-3 quotient**
(`Mod2Cohomology.ComparisonDatum`), because no genuine Čech cohomology existed yet.  Task 6 has
now built the standard carrier `CechZ2.Cohomology 𝓤.U 2 = Ȟ²(𝓤;ℤ₂)`, so the remaining
dependency can be named exactly:

`Φ_𝓤 : Ȟ²(𝓤;ℤ₂) →ₗ[ℤ₂] H²_sing(X;ℤ₂)`,

`ℤ₂`-linear, and natural in refinements of the cover.  `CechSingularSpec.Comparison` below is
precisely that datum, and nothing more: it is an ordinary structure taken as an explicit
hypothesis.  **It is not constructed here, it is not an axiom, and nothing in the Spine
consumes it.**  The old Task-5 specification is left in place, untouched.

## What a construction of `Φ_𝓤` needs (audit of the routes)

* **Route A — nerve/good-cover.**  Build the map by subdividing a singular simplex against the
  cover (Lebesgue-number / barycentric-subdivision argument), or by the nerve theorem.  The
  comparison is an *isomorphism* only under an acyclicity hypothesis on the overlaps (good
  cover); the *map* itself needs the subdivision machinery: small singular chains, the
  small-simplices theorem `H_*(small) ≅ H_*`, and a partition-of-unity or Lebesgue-number
  argument on a paracompact/metrisable base.  None of these is available in the pinned library
  for singular *cochains* with `ZMod 2` coefficients as constructed in Task 5; each would have
  to be built natively, exactly as the two complexes were.
* **Route B — direct-limit Čech theory.**  Construct `Ȟ*(X) = colim_𝓤 Ȟ*(𝓤)` first (the
  refinement pullbacks `CechZ2.Hmap`, together with `Hmap_id`/`Hmap_comp`, are already the
  functoriality this needs), then compare with singular cohomology.  Task 6 deliberately does
  *not* take the colimit; that is the explicit non-goal of this task.
* **Route C — sheaf cohomology.**  Mathlib has sheaf cohomology of abelian sheaves, and a
  comparison would go through the constant sheaf `ℤ₂` and a Čech-to-derived-functor spectral
  sequence, plus the identification of sheaf cohomology with singular cohomology on locally
  contractible spaces.  The last step is *not* in the pinned library, so this route is not
  materially shorter than Route A and would additionally force the Task-5 singular carrier to
  be compared with a second, foreign, carrier.

The minimal next theorem is therefore, in Route A form:

> for a cover `𝓤` of `X`, a `ℤ₂`-linear map `Č²(𝓤;ℤ₂) → C²_sing(X;ℤ₂)` sending Čech cocycles to
> singular cocycles and Čech coboundaries to singular coboundaries.

Everything else in this file is the bookkeeping that such a map would immediately provide.
-/

noncomputable section

namespace CechSingularSpec

open CategoryTheory CechSpinLift CechZ2 CechSpinZ2 NullSectorTask28

universe u t

/-- **WP12, the exact missing map.**  A comparison datum for a space `X`: a `ℤ₂`-linear map
from fixed-cover Čech cohomology in degree two into the Task-5 singular carrier, for every
cover, compatible with refinement pullbacks.

This is a hypothesis, never a theorem of this project. -/
structure Comparison (X : TopCat.{u}) where
  /-- The comparison map `Φ_𝓤` for each open cover of `X`. -/
  map : ∀ {ι : Type t} (𝓤 : CechCover (↥X) ι),
    CechZ2.Cohomology 𝓤.U 2 →ₗ[ZMod 2] Mod2Cohomology.Cohomology X 2
  /-- Naturality in refinements: refining the cover does not change the singular image. -/
  refinement_compat : ∀ {ι ι' : Type t} (𝓤 : CechCover (↥X) ι) (𝓥 : CechCover (↥X) ι')
    (R : CoverRefinement 𝓥 𝓤) (q : CechZ2.Cohomology 𝓤.U 2),
    map 𝓥 (CechZ2.Hmap R.le 2 q) = map 𝓤 q

variable {X : TopCat.{u}} {ι ι' : Type t} {𝓤 : CechCover (↥X) ι} {𝓥 : CechCover (↥X) ι'}
  {T : VisibleCocycle (↥SpinCore.GLor) 𝓤}

/-- **Conditional transport.**  Given the missing comparison, the Task-6 Spin-lift Čech class
determines a genuine singular mod-2 class.  This is a definition of what would follow, not a
construction of the comparison. -/
def transport (C : Comparison.{u, t} X) {D : SpinLiftFamily SpinCore.internalSpinProjection T}
    (V : ConstOn₃ 𝓤 D.defect) : Mod2Cohomology.Cohomology X 2 :=
  C.map 𝓤 (spinLiftCechClass V)

/-- A vanishing Čech class has vanishing singular image (the converse needs injectivity of the
comparison, which is *not* part of the datum: that is precisely the good-cover input). -/
theorem transport_eq_zero (C : Comparison.{u, t} X)
    {D : SpinLiftFamily SpinCore.internalSpinProjection T} (V : ConstOn₃ 𝓤 D.defect)
    (h : spinLiftCechClass V = 0) : transport C V = 0 := by
  rw [transport, h, map_zero]

/-- The singular image would be insensitive to refinement, by naturality together with the
Task-6 refinement theorem `CechSpinZ2.Hmap_spinCechClass`. -/
theorem transport_refinement (C : Comparison.{u, t} X) (R : CoverRefinement 𝓥 𝓤)
    {D : SpinLiftFamily SpinCore.internalSpinProjection T} (V : ConstOn₃ 𝓤 D.defect) :
    transport C (V.pull R) = transport C V := by
  show C.map 𝓥 (spinCechClass spinKernelSign (V.pull R))
      = C.map 𝓤 (spinCechClass spinKernelSign V)
  rw [← Hmap_spinCechClass spinKernelSign R V]
  exact C.refinement_compat 𝓤 𝓥 R _

end CechSingularSpec
