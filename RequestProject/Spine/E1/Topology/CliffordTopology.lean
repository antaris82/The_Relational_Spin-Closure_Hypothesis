import Mathlib
import RequestProject.Spine.E1.Topology.FiniteDimTools
import RequestProject.Spine.E1.CliffordMonomial

/-!
# Spine / E1 / Topology : the canonical topology of the intrinsic Clifford algebra

This is the first module of the topological layer of the intrinsic experiment-1 spin core.
It equips the intrinsic real Clifford algebra `SpinCore.Cl3 = CliffordAlgebra q3` with a
topology and proves that this topology makes it a Hausdorff topological ring.

**Canonicality.**  The topology is *not chosen*: it is Mathlib's `moduleTopology ℝ Cl3`,
the finest topology making addition and the real scalar action continuous.  This is a
choice-free construction from the `ℝ`-module structure of `Cl₃(ℝ)` alone (an `sInf` over a
set of topologies): no basis, no norm, no matrix model and no representation enters the
*definition*.  The eight-monomial frame of `RequestProject.Spine.E1.CliffordMonomial` is
used only to *prove* finiteness and Hausdorffness; it does not occur in the definition.

Contents:

* `SpinCore.monoBasis` — the eight monomials `1, e₀, e₁, e₂, e₀e₁, e₀e₂, e₁e₂, ω` as an
  `ℝ`-basis of `Cl₃(ℝ)` (packaging of the already proved spanning and independence);
* `Module.Finite ℝ Cl3`, `FiniteDimensional ℝ Cl3`, `SpinCore.finrank_Cl3` (`= 8`);
* the instances `TopologicalSpace Cl3 := moduleTopology ℝ Cl3` and `IsModuleTopology ℝ Cl3`;
* `IsTopologicalRing Cl3` — from Mathlib's theorem that a module-topologised algebra which
  is finite over a topological base ring is a topological ring;
* `T2Space Cl3` — through the coordinate map of the monomial basis;
* `SpinCore.continuous_linearMap_Cl3` — every `ℝ`-linear map out of `Cl₃(ℝ)` is continuous;
  in particular `SpinCore.continuous_reverse` and `SpinCore.continuous_involute`
  (Clifford conjugation is handled in the spin-group layer, which is where it is defined);
* `SpinCore.Cl3_topology_unique` — the canonicality statement: *any* topology on `Cl₃(ℝ)`
  making it a Hausdorff topological real vector space is the one installed here.

**Import firewall.**  `Mathlib`, the generic finite-dimensional tools, and the intrinsic
Clifford layer only.  No `SL(2,ℂ)`, no complex matrix model, no `RequestProject.Spine.E2`,
no historical experiment module.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-! ## The monomial basis and finite dimensionality -/

/-- The eight monomials are linearly independent over `ℝ`. -/
theorem linearIndependent_mono : LinearIndependent ℝ mono :=
  Fintype.linearIndependent_iff.2 fun c hc i => monoComb_coeffs_eq_zero c hc i

/-- **The monomial basis of `Cl₃(ℝ)`.**  Packaging of the already proved spanning
(`SpinCore.monoSpan_eq_top`) and independence (`SpinCore.monoComb_coeffs_eq_zero`). -/
def monoBasis : Module.Basis (Fin 8) ℝ Cl3 :=
  Module.Basis.mk linearIndependent_mono (le_of_eq monoSpan_eq_top.symm)

@[simp] theorem monoBasis_apply (i : Fin 8) : monoBasis i = mono i :=
  Module.Basis.mk_apply _ _ i

instance instModuleFiniteCl3 : Module.Finite ℝ Cl3 := Module.Finite.of_basis monoBasis

instance instFiniteDimensionalCl3 : FiniteDimensional ℝ Cl3 := instModuleFiniteCl3

theorem finrank_Cl3 : Module.finrank ℝ Cl3 = 8 := by
  rw [Module.finrank_eq_card_basis monoBasis]
  simp

/-! ## The canonical topology -/

/-- **The canonical topology of the intrinsic Clifford algebra.**  It is the module
topology of `Cl₃(ℝ)` as a real vector space: the finest topology for which addition and the
real scalar action are continuous.  The definition uses no basis and no auxiliary model. -/
instance instTopologicalSpaceCl3 : TopologicalSpace Cl3 := moduleTopology ℝ Cl3

instance instIsModuleTopologyCl3 : IsModuleTopology ℝ Cl3 := ⟨rfl⟩

instance instContinuousAddCl3 : ContinuousAdd Cl3 := IsModuleTopology.toContinuousAdd ℝ Cl3

/-- `Cl₃(ℝ)` is a topological ring: multiplication is continuous because it is `ℝ`-bilinear
on a module-topologised finite `ℝ`-algebra. -/
instance instIsTopologicalRingCl3 : IsTopologicalRing Cl3 :=
  IsModuleTopology.isTopologicalRing ℝ Cl3

/-- The coordinate map attached to the monomial basis. -/
def monoCoords : Cl3 ≃ₗ[ℝ] (Fin 8 → ℝ) := monoBasis.equivFun

theorem continuous_monoCoords : Continuous (⇑monoCoords) := by
  have h := IsModuleTopology.continuous_of_linearMap
    (R := ℝ) (monoCoords : Cl3 →ₗ[ℝ] (Fin 8 → ℝ))
  simpa using h

/-- `Cl₃(ℝ)` is Hausdorff: the monomial coordinate map is a continuous injection into
`ℝ⁸`. -/
instance instT2SpaceCl3 : T2Space Cl3 :=
  T2Space.of_injective_continuous monoCoords.injective continuous_monoCoords

/-- **The topology is the expected one.**  The monomial coordinate map is a homeomorphism
`Cl₃(ℝ) ≃ₜ ℝ⁸`.  In particular the canonical topology is neither discrete nor indiscrete:
it is the usual eight-dimensional real topology read in the intrinsic monomial frame. -/
def monoHomeomorph : Cl3 ≃ₜ (Fin 8 → ℝ) where
  toEquiv := monoCoords.toEquiv
  continuous_toFun := continuous_monoCoords
  continuous_invFun := by
    have h := IsModuleTopology.continuous_of_linearMap
      (R := ℝ) (monoCoords.symm : (Fin 8 → ℝ) →ₗ[ℝ] Cl3)
    simpa using h

/-! ## Continuity of the linear structure maps -/

/-- Every `ℝ`-linear map out of `Cl₃(ℝ)` is continuous (into any topological `ℝ`-module):
an instance of the universal property of the module topology. -/
theorem continuous_linearMap_Cl3 {B : Type*} [AddCommGroup B] [Module ℝ B]
    [TopologicalSpace B] [ContinuousAdd B] [ContinuousSMul ℝ B] (f : Cl3 →ₗ[ℝ] B) :
    Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

/-- Clifford reversion is continuous. -/
theorem continuous_reverse : Continuous (fun x : Cl3 => reverse (Q := q3) x) := by
  have h := continuous_linearMap_Cl3 (reverse (Q := q3))
  simpa using h

/-- The grade involution is continuous. -/
theorem continuous_involute : Continuous (fun x : Cl3 => involute (R := ℝ) (Q := q3) x) := by
  have h := continuous_linearMap_Cl3 (involute (R := ℝ) (Q := q3)).toLinearMap
  simpa using h

/-! ## Canonicality

The topology above is not one choice among many: a finite-dimensional real vector space
carries exactly one Hausdorff topological-vector-space topology, and it is the module
topology.  Consequently *any* topology on `Cl₃(ℝ)` for which it is a Hausdorff topological
real vector space is the one installed here. -/

/-- **Uniqueness of the topology on `Cl₃(ℝ)`.**  Any Hausdorff topological
`ℝ`-vector-space topology on `Cl₃(ℝ)` equals the module topology installed above.  Hence
the topological structure of this layer is forced by the algebraic data, not chosen. -/
theorem Cl3_topology_unique (t : TopologicalSpace Cl3)
    (hgrp : @IsTopologicalAddGroup Cl3 t _) (hsmul : @ContinuousSMul ℝ Cl3 _ _ t)
    (ht2 : @T2Space Cl3 t) : t = instTopologicalSpaceCl3 :=
  SpineTop.eq_moduleTopology_of_t2 Cl3 t hgrp hsmul ht2

end SpinCore
