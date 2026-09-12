import RequestProject.Spine.E2.Cech.Refinement
import RequestProject.Spine.E2.SpinProjection

/-!
# Task 3, WP10 : instantiation with the native intrinsic Spin projection

Everything in the Task-3 layer is proved for an *arbitrary* `InternalProjection L G` with a
central discrete kernel and continuous local sections.  This module instantiates it with the
native intrinsic Spin projection of the spine,

`SpinCore.internalSpinProjection : InternalProjection ↥SpinGroup ↥GLor`,

whose kernel is exactly the central `{±1}` of the intrinsic spin group.  The concrete
consequence is that the triple-overlap defect of local Spin lifts of `GLor`-valued transition
data takes values in `{1, negOneSpin}` — a genuine `ℤ₂`.

**Import discipline.**  The import closure of this module contains only `Mathlib` and modules
of `RequestProject.Spine`; in particular no module of `RequestProject.Experiment1` or
`RequestProject.Experiment2`, and no historical Task-23 infrastructure.  The mechanical check
is `RequestProject.Spine.Audit.Firewall`.

**Not claimed.**  `X` is an arbitrary topological space and the transition data is arbitrary:
there is no manifold, no tangent bundle, no frame bundle, no metric and no orientation here.
The class constructed below is therefore *not* identified with `w₂(TM)`; it is an abstract
`ℤ₂`-valued Spin-lift obstruction of the correct formal type for a later comparison.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinCore

open CechSpinLift NullSectorTask28

universe w t

variable {X : Type w} [TopologicalSpace X] {ι : Type t} {𝓤 : CechCover X ι}
  {T : VisibleCocycle (↥GLor) 𝓤}

/-- **DERIVED_NATIVE (WP10), principal.**  For the native Spin projection the triple-overlap
defect is `±1`: it lies in the exact intrinsic kernel `{1, negOneSpin}`.

The proof chain is: visible Čech 1-cocycle law → the two internal representatives
`g̃_ij g̃_jk` and `g̃_ik` of the same visible map → the inherited relative-factor theorem →
`ρ (c_ijk) = 1` → the exact kernel theorem `SpinCore.mem_ker_spinCover_iff`. -/
theorem cech_defect_eq_pm_one (D : SpinLiftFamily internalSpinProjection T) (i j k : ι)
    {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) :
    D.defect i j k x = 1 ∨ D.defect i j k x = negOneSpin := by
  have h : D.defect i j k x ∈ spinCover.ker := D.defect_mem_ker i j k hx
  exact (mem_ker_spinCover_iff _).1 h

/-- **DERIVED_NATIVE (WP10).**  The intrinsic kernel really has two elements, so the defect
is genuinely `ℤ₂`-valued and not trivially valued. -/
theorem cech_defect_kernel_card :
    Nat.card (internalSpinProjection.Ker : Subgroup ↥SpinGroup) = 2 :=
  spinCover_ker_card

/-- **DERIVED_NATIVE (WP10), principal endpoint — `SpinLiftObstruction` for the native
intrinsic Spin projection.**

For an arbitrary topological base `X`, an arbitrary open cover `𝓤`, arbitrary `GLor`-valued
transition data satisfying the exact Čech 1-cocycle law, and *any* family of continuous local
Spin lifts on the double overlaps:

1. the triple-overlap defect `c_ijk = g̃_ij g̃_jk g̃_ik⁻¹` is `±1`-valued;
2. it is continuous, hence locally constant, on every triple overlap;
3. it satisfies the multiplicative Čech 2-cocycle law on every quadruple overlap;
4. changing the local Spin representatives multiplies it by a Čech 1-coboundary;
5. its class on the fixed cover is independent of that choice;
6. the class is trivial **iff** coherent Spin-valued transition data exists;
7. the class is natural under cover refinement.

No `SL(2,ℂ)` model, no historical experiment module and no external covering-space input is
used anywhere in the chain. -/
theorem spinLiftObstruction (D : SpinLiftFamily internalSpinProjection T) :
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k,
        D.defect i j k x = 1 ∨ D.defect i j k x = negOneSpin) ∧
    (∀ i j k, ContinuousOn (D.defect i j k) (𝓤.overlap₃ i j k)) ∧
    (∀ i j k, IsLocallyConstant
        (internalSpinProjection.toKerFun (D.defect_isKerFunOn i j k))) ∧
    (∀ i j k l, ∀ x ∈ 𝓤.overlap₄ i j k l,
        D.defect j k l x * (D.defect i k l x)⁻¹ * D.defect i j l x
          * (D.defect i j k x)⁻¹ = 1) ∧
    (∀ D' : SpinLiftFamily internalSpinProjection T,
        ∃ ε : ι → ι → (X → ↥SpinGroup), IsKerCochain₁ internalSpinProjection 𝓤 ε ∧
          (∀ i j, D'.lift i j = fun x => ε i j x * D.lift i j x) ∧
          ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k,
            D'.defect i j k x = delta₁ ε i j k x * D.defect i j k x) ∧
    (∀ D' : SpinLiftFamily internalSpinProjection T, D.obstruction = D'.obstruction) ∧
    (D.obstruction = trivialClass internalSpinProjection 𝓤 ↔
      ∃ D' : SpinLiftFamily internalSpinProjection T, D'.IsCoherent) ∧
    (∀ {ι' : Type t} {𝓥 : CechCover X ι'} (R : CoverRefinement 𝓥 𝓤),
        (D.pullLift R).obstruction = restrictClass internalSpinProjection R D.obstruction) :=
  ⟨fun i j k _ hx => cech_defect_eq_pm_one D i j k hx,
   fun i j k => D.defect_continuousOn i j k,
   fun i j k => D.defect_isLocallyConstant i j k,
   fun i j k l _ hx => D.defect_delta_eq_one i j k l hx,
   fun D' => D.defect_change_of_lift D',
   fun D' => D.obstruction_lift_independent D',
   D.obstruction_eq_trivialClass_iff_exists_coherent,
   fun R => D.obstruction_pullLift R⟩

end SpinCore

/-! ## Axiom audit of the Task-3 endpoints -/

#print axioms CechSpinLift.SpinLiftFamily.spinLiftObstruction_defect
#print axioms CechSpinLift.SpinLiftFamily.defect_change_of_lift
#print axioms CechSpinLift.SpinLiftFamily.obstruction_lift_independent
#print axioms CechSpinLift.SpinLiftFamily.obstruction_eq_trivialClass_iff_exists_coherent
#print axioms CechSpinLift.SpinLiftFamily.obstruction_pullLift
#print axioms SpinCore.cech_defect_eq_pm_one
#print axioms CechSpinLift.SpinLiftFamily.obstruction_pullLift_indep_of_map
#print axioms SpinCore.spinLiftObstruction
