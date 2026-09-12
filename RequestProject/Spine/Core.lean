import RequestProject.Spine.E1.Core
import RequestProject.Spine.E1.SL2Comparison
import RequestProject.Spine.E2.Core
import RequestProject.Spine.E2.SpinProjection
import RequestProject.Spine.E2.SpinProjectionIntegration
import RequestProject.Spine.E2.Cech.Core
import RequestProject.Spine.Geometry.Core
import RequestProject.Spine.Cohomology.Core
import RequestProject.Spine.Cech.Core
import RequestProject.Spine.GoodCover.Core
import RequestProject.Spine.Nerve.Core

/-!
# Spine / Core : the aggregate production endpoint of the new project

This module collects the two halves of the new, self-contained spine:

* `RequestProject.Spine.E1.Core` — the intrinsic algebraic reconstruction
  `LorentzCarrier → LorentzQuadratic → LorentzClifford → SpinGroup → spinCover → SpinKernel`,
  together with the Clifford-module layer, and `RequestProject.Spine.E1.SL2Comparison`, the
  downstream comparison with `SL(2,ℂ)`;
* `RequestProject.Spine.E2.Core` — the generic lift theory: the central double-cover
  interface `NullSectorTask28.InternalProjection`, transition systems, local internal
  representatives, kernel ambiguity, the triple-overlap defect, descent, the global glued
  object, the defect classification and the atlas-change layer.  Every theorem of that half
  is parameterized by an arbitrary internal projection `P`; no concrete model is fixed.

**Legacy independence.**  The transitive import closure of this module contains only
`Mathlib` and modules of `RequestProject.Spine`.  In particular it contains no module of
`RequestProject.Experiment1` or `RequestProject.Experiment2`; the mechanical check is
`RequestProject.Spine.Audit.Firewall`.

**Controls are downstream.**  The native controls live under `RequestProject.Spine.Controls`
and are *not* imported here: production never depends on a control.

**The E1 → E2 bridge is now closed, natively.**  The *topological qualification* of the
intrinsic spin cover is part of the E1 half (`RequestProject.Spine.E1.Topology.Core`): the
canonical topology of `Cl₃(ℝ)`, Hausdorff topological-group structures on
`SpinCore.SpinGroup` and `SpinCore.GLor`, continuity of `SpinCore.spinCover` and
discreteness of its `{±1}` kernel, bundled as `SpinCore.topologicalSpinProjection`.  On top
of it, `RequestProject.Spine.E1.Topology.LocalSection` constructs **continuous local
sections** of `spinCover` around every point of `GLor` — by an explicit algebraic inversion
of the twisted Clifford action, with no `SL(2,ℂ)` input and no postulated covering-map
property — together with the local two-sheet decomposition.  `SpinCore.internalSpinProjection`
(`RequestProject.Spine.E2.SpinProjection`) is the resulting native instance of the generic
interface `NullSectorTask28.InternalProjection`, and
`RequestProject.Spine.E2.SpinProjectionIntegration` is the integration test showing that the
generic lift theory consumes it.

**The Task-3 layer.**  `RequestProject.Spine.E2.Cech.Core` is the endpoint of the abstract
Čech layer built on top of the native projection: open covers of an abstract topological
base, visible transition data with the exact Čech 1-cocycle law, families of local Spin
lifts, the kernel-valued triple-overlap defect with its 2-cocycle law, the coboundary law
under change of local representatives, the lift-choice-independent fixed-cover obstruction
class, the theorem `[c] = 1 ↔ coherent Spin-valued transition data exists`, refinement
naturality, and the instantiation with `SpinCore.internalSpinProjection` giving
`c_ijk ∈ {±1}`.  The class of that layer is **not** identified with `w₂(TM)`; no manifold,
tangent bundle, metric, orientation or frame bundle occurs anywhere below it.

**The Task-4 layer.**  `RequestProject.Spine.Geometry.Core` is the endpoint of the first
geometric layer: oriented, time-oriented, Lorentz-orthonormal local frame data (instantiated
with the tangent spaces of a smooth four-manifold modelled on the intrinsic carrier), the
derived `GLor`-valued frame transition cocycle, the Task-3 obstruction instantiated on it,
the Čech notion of a Spin structure, the theorem `[c]_frame = 0 ↔ a Spin structure exists`,
the fixed-cover torsor statement for Spin structures, and the canonical additive
`ℤ₂`-valued Čech presentation of the class.  That class is still **not** identified with
`w₂(TM)` — the pinned library has no Stiefel–Whitney classes and no `H²(M;ℤ₂)`, so the
identification cannot be stated; the exact status is recorded in `TASK04_AUDIT.md`.

**The Task-5 layer.**  `RequestProject.Spine.Cohomology.Core` is the endpoint of the native
mod-2 singular cohomology layer: singular cochains `Cⁿ(X;ℤ₂)` built on Mathlib's singular
simplicial set, the coboundary with the theorem `δ² = 0`, the genuine quotient
`Hⁿ(X;ℤ₂) = Zⁿ/Bⁿ`, functorial pullbacks, the Alexander–Whitney cup product with its Leibniz
rule and the descended products `H¹ × H¹ → H²`, `H² × H² → H⁴`.  It is *independent* of the
Čech layer above: the Task-3/Task-4 obstruction class is **not** identified with a singular
cohomology class, and `RequestProject.Spine.Cohomology.CechBridgeSpec` only records, as an
explicit hypothesis, what a future comparison theorem would have to supply.

**The Task-6 layer.**  `RequestProject.Spine.Cech.Core` is the endpoint of the native
fixed-cover Čech layer: the nerve of an indexed family of subsets, Čech cochains
`Čⁿ(𝓤;ℤ₂)` with constant `ℤ₂` coefficients, the coboundary with the theorem `δ_Č² = 0`, the
genuine quotient `Ȟⁿ(𝓤;ℤ₂) = Žⁿ/B̌ⁿ`, the refinement pullback with its functoriality, and — on
top of that Spin-independent complex — the translation of the Task-3 Spin-lift defect into a
genuine Čech 2-cocycle, the change-of-lift coboundary law, the lift-independent class
`[z] ∈ Ȟ²(𝓤;ℤ₂)`, the vanishing criterion in standard Čech language, refinement naturality, and
the canonical *injective* comparison map `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤` (which is **not**
surjective in general).  `RequestProject.Spine.Cech.SingularBridgeSpec` records, as an explicit
hypothesis, the exact remaining map `Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)`.  No good cover is assumed
anywhere, no direct limit over covers is taken, and `[z]` is **not** identified with `w₂(TM)`.

**Not claimed here.**  Everything above the local theory: a global section, covering-space
structure over the whole group, principal frame bundles as total spaces, `w₁`, `w₂`, spinor
bundles, solder forms, connections, curvature, torsion.
-/
