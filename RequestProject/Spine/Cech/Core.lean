import RequestProject.Spine.Cech.Cochain
import RequestProject.Spine.Cech.Coboundary
import RequestProject.Spine.Cech.Cohomology
import RequestProject.Spine.Cech.Refinement
import RequestProject.Spine.Cech.CoverNerve
import RequestProject.Spine.Cech.KernelSign
import RequestProject.Spine.Cech.SpinKernelSign
import RequestProject.Spine.Cech.SpinCocycle
import RequestProject.Spine.Cech.Comparison
import RequestProject.Spine.Cech.SpinInstance
import RequestProject.Spine.Cech.SingularBridgeSpec

/-!
# Spine / Cech : native fixed-cover Čech `ℤ₂`-cohomology and the Spin-lift class (Task 6)

This module is the endpoint of the Task-6 layer.

## The Spin-independent half (WP2–WP4, WP11)

* `Cochain.lean` — the nerve of an indexed family `U : ι → Set X` (tuples with nonempty
  overlap), the face operators, and `Čⁿ(U;ℤ₂) = Nerve U n → ZMod 2` with its derived
  `ZMod 2`-module structure.  Imports Mathlib only: no group, no projection, no lift, no
  defect is in scope.
* `Coboundary.lean` — the coboundary `δ_Č`, its agreement with the conventional alternating
  formula (`coboundary_eq_alternating`, the signs collapse because `-1 = 1` in `ZMod 2`), and
  the **theorem `δ_Č² = 0`**, proved from the `Fin.succAbove` simplicial identity.
* `Cohomology.lean` — `Žⁿ = ker δ`, `B̌ⁿ = im δ`, the theorem `B̌ⁿ ⊆ Žⁿ`, and the genuine
  quotient `Ȟⁿ(U;ℤ₂) = Žⁿ/B̌ⁿ`; `Ȟ¹` and `Ȟ²` are instances of it.
* `Refinement.lean` — the refinement pullback `r* : Ȟⁿ(U;ℤ₂) → Ȟⁿ(V;ℤ₂)` with its two
  functoriality laws.

## The bridge to the Task-3 Spin-lift defect (WP5–WP10)

* `CoverNerve.lean` — the Task-3 cover `CechSpinLift.CechCover` seen as a nerve; the two- and
  three-fold overlaps of Task 3 are *proved equal* to the nerve overlaps, so no second cover
  model is introduced.
* `KernelSign.lean`, `SpinKernelSign.lean` — the kernel dictionary `ker ρ ≅ ℤ₂` as data
  (`+1 ↦ 0`, `-1 ↦ 1`, multiplication ↦ addition), instantiated for the intrinsic Spin
  projection by *reusing* the Task-4 sign map `LorentzFrames.spinSign`.
* `SpinCocycle.lean` — the Task-3 defect as a genuine Čech 2-cochain, the cocycle law
  `δ_Č z = 0` derived from the Task-3 quadruple-overlap identity, the change-of-lift law
  `z' = z + δ_Č a`, the lift-independent class `[z] ∈ Ȟ²(𝓤;ℤ₂)`, and the vanishing criterion
  `[z] = 0 ↔ coherent Spin lifts exist` (on covers with preconnected double overlaps).
* `Comparison.lean` — the canonical map `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤`, its injectivity on
  covers with preconnected double overlaps, the proof that it is *not* surjective in general,
  the agreement of the two classes and of their vanishing, and refinement naturality.
* `SpinInstance.lean` — the intrinsic Spin and Lorentz-frame instantiations.
* `SingularBridgeSpec.lean` — WP12: the exact specification of the still-missing map
  `Φ_𝓤 : Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)`, as a hypothesis, with the audit of the possible routes.

## What is *not* claimed

No direct-limit Čech cohomology of the space, no sheaf cohomology, no Čech–singular comparison
theorem, no good-cover assumption anywhere in the construction, no Stiefel–Whitney class and no
identification `[z] = w₂(TM)`.  The class `[z]` is a fixed-cover topological Spin-lift
obstruction, and nothing else.
-/

/-! ## Axiom audit of the Task-6 principal declarations

Each of the following must report only `[propext, Classical.choice, Quot.sound]`. -/

#print axioms CechZ2.Cochain
#print axioms CechZ2.coboundary_eq_alternating
#print axioms CechZ2.coboundary_coboundary
#print axioms CechZ2.d_comp_d
#print axioms CechZ2.coboundaries_le_cocycles
#print axioms CechZ2.Cohomology
#print axioms CechZ2.mk_eq_zero_iff
#print axioms CechZ2.pull_d
#print axioms CechZ2.Hmap
#print axioms CechZ2.Hmap_id
#print axioms CechZ2.Hmap_comp
#print axioms CechSpinZ2.KernelSign
#print axioms CechSpinZ2.KernelSign.kerMulEquiv
#print axioms CechSpinZ2.spinKernelSign
#print axioms CechSpinZ2.zCochain
#print axioms CechSpinZ2.zCochain_apply
#print axioms CechSpinZ2.d_zCochain
#print axioms CechSpinZ2.spinCechClass
#print axioms CechSpinZ2.zCochain_change_of_lift
#print axioms CechSpinZ2.spinCechClass_lift_independent
#print axioms CechSpinZ2.spinCechClass_eq_zero_iff_exists_coherent
#print axioms CechSpinZ2.toObstruction
#print axioms CechSpinZ2.toObstruction_spinCechClass
#print axioms CechSpinZ2.toObstruction_injective
#print axioms CechSpinZ2.classOf_not_mem_range_toObstruction
#print axioms CechSpinZ2.spinCechClass_eq_zero_iff_obstruction_eq_trivial
#print axioms CechSpinZ2.Hmap_spinCechClass
#print axioms CechSpinZ2.spinCechClass_pull_indep_of_map
#print axioms CechSpinZ2.spinLiftCechClass
#print axioms CechSpinZ2.spinLiftCechClass_eq_zero_iff_exists_coherent
#print axioms CechSpinZ2.frameCechClass_eq_zero_iff_spinStructure
#print axioms CechSingularSpec.transport_refinement
