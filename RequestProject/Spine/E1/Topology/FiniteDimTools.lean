import Mathlib

/-!
# Spine / E1 / Topology : generic finite-dimensional topological tools

This module contains **no project-specific mathematics**.  It records two general facts
about the *module topology* of Mathlib
(`moduleTopology R A`, the finest topology making addition and the `R`-action continuous)
that the intrinsic topological spin layer uses:

* `SpineTop.eq_moduleTopology_of_t2` — on a finite-dimensional real vector space there is
  exactly one Hausdorff topological-vector-space topology, namely the module topology.
  This is the precise sense in which the topologies installed downstream are *forced* by
  the algebraic data rather than chosen;
* `SpineTop.continuous_into_linearMap` — a map into a space of linear maps carrying the
  module topology is continuous as soon as all its evaluations at a fixed finite basis are
  continuous.

Both are consequences of Mathlib results only (`isModuleTopologyOfFiniteDimensional`,
`IsModuleTopology.continuous_of_linearMap`, `IsModuleTopology.instPi`); the module is
imported by the topological spin layer and imports nothing but `Mathlib`.
-/

noncomputable section

namespace SpineTop

/-- **Uniqueness of the finite-dimensional topology.**  If a finite-dimensional real vector
space carries a topology making it a Hausdorff topological vector space, then that topology
*is* the module topology.  Hence no inequivalent alternative exists inside the class of
Hausdorff topological-vector-space topologies. -/
theorem eq_moduleTopology_of_t2 (E : Type*) [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (t : TopologicalSpace E)
    (hgrp : @IsTopologicalAddGroup E t _) (hsmul : @ContinuousSMul ℝ E _ _ t)
    (ht2 : @T2Space E t) : t = moduleTopology ℝ E := by
  letI := t
  haveI := hgrp
  haveI := hsmul
  haveI := ht2
  haveI : IsModuleTopology ℝ E := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology ℝ E

/-- A finite-dimensional real vector space carrying the module topology is Hausdorff.  (A
basis is used in the proof only; the topology itself is basis-free.) -/
theorem t2Space_of_isModuleTopology (E : Type*) [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace E] [IsModuleTopology ℝ E] : T2Space E := by
  set b := Module.finBasis ℝ E with hb
  have hcont : Continuous (⇑b.equivFun) := by
    have h := IsModuleTopology.continuous_of_linearMap
      (R := ℝ) (b.equivFun : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ))
    simpa using h
  exact T2Space.of_injective_continuous b.equivFun.injective hcont

/-- **Evaluation criterion for continuity into a space of linear maps.**  If `E` has a
finite basis and both `E → F` linear maps and `F` carry the module topology, then a family
of linear maps depending on a parameter is continuous as soon as each basis evaluation
is. -/
theorem continuous_into_linearMap {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsModuleTopology ℝ F]
    [TopologicalSpace (E →ₗ[ℝ] F)] [IsModuleTopology ℝ (E →ₗ[ℝ] F)]
    (b : Module.Basis ι ℝ E) (f : X → (E →ₗ[ℝ] F))
    (h : ∀ i, Continuous fun x => f x (b i)) : Continuous f := by
  haveI : ContinuousAdd F := IsModuleTopology.toContinuousAdd ℝ F
  haveI : ContinuousAdd (E →ₗ[ℝ] F) := IsModuleTopology.toContinuousAdd ℝ (E →ₗ[ℝ] F)
  set e : (ι → F) ≃ₗ[ℝ] (E →ₗ[ℝ] F) := b.constr ℝ with he
  have hcont : Continuous (⇑e) := by
    have h' := IsModuleTopology.continuous_of_linearMap
      (R := ℝ) (e : (ι → F) →ₗ[ℝ] (E →ₗ[ℝ] F))
    simpa using h'
  have hfe : f = e ∘ (fun x i => f x (b i)) := by
    funext x
    refine (e.eq_symm_apply.1 ?_).symm
    funext i
    rfl
  rw [hfe]
  exact hcont.comp (continuous_pi h)

end SpineTop
