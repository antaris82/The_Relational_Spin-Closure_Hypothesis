import Mathlib
import RequestProject.Spine.E1.SpinKernel
import RequestProject.Spine.E1.Topology.Core
import RequestProject.Spine.E1.WeylSpinorModule

/-!
# Spine / E1 : the principal endpoint of the intrinsic spin-reconstruction core

This module is the **principal production endpoint** of the experiment-1 half of the
spin-reconstruction spine.  It adds no new mathematics; it collects, under stable names,
the results the later stages of the reconstruction programme are meant to consume, and it
records their axiom audit.

Chain, all stated on the intrinsic real carrier `SpinCore.LorentzCarrier = ℝ ⊕ ℝ³`:

1. **derived Lorentz quadratic structure** — `SpinCore.NS` with `NS x = x₀² - |x⃗|²`
   (`SpinCore.NS_def`), its polarization `SpinCore.BS`, the intrinsic square cone
   `SpinCore.ConeS`, and the intrinsic Lorentz group `SpinCore.GLor`;
2. **Clifford algebra** — `SpinCore.Cl3 = CliffordAlgebra q3` over the Euclidean part, the
   even Lorentz Clifford map `SpinCore.evenToCl3`, and the paravector embedding
   `SpinCore.spinToCl`;
3. **spin group and double cover** — the predicate `SpinCore.IsSpinElem`, the bundled group
   `SpinCore.SpinGroup : Subgroup Cl3ˣ`, the induced action `SpinCore.spinLor`, the
   homomorphism `SpinCore.spinCover : SpinGroup →* GLor`, and both
   `spin_double_cover_of_lorentz` (unbundled) and `SpinCore.spin_double_cover` (bundled):
   the cover is surjective with central kernel exactly `{±1}`;
4. **topological qualification** — the canonical (module) topology of `Cl₃(ℝ)`, the
   inherited Hausdorff topological-group structures on `SpinCore.SpinGroup` and
   `SpinCore.GLor`, continuity of `SpinCore.spinCover` and discreteness of its kernel
   (`SpinCore.spin_double_cover_topological`, `SpinCore.topologicalSpinProjection`);
5. **Clifford modules** — `SpinCore.CliffordAction` with the concrete Weyl module
   (`SpinCore.weylAction`, `SpinCore.weyl_chirality`).

**Import firewall.**  The transitive closure of this module contains only `Mathlib` and
modules of `RequestProject.Spine.E1`.  In particular it contains none of

* the historical Hermitian Jordan-carrier layer (`Herm2`, `Task6*`, `Task7*`, `Task8*`,
  `Task9Freeze`, `Task9Wide`, `SpinFinal`, …);
* the Maxwell / gauge-field / quantization / mass-selection / positive-frequency branches;
* any experiment-2 module.

The mechanical check is `RequestProject.Spine.Audit.E1Firewall`.

**Not claimed here.**  Nothing in this module concerns continuous local sections of the
cover, manifolds, orientation or time orientation, global spin lifts, Stiefel–Whitney
classes, spinor bundles or connections.
-/

noncomputable section

namespace SpinCore

/-! ## 1. The derived Lorentz quadratic structure -/

/-- The intrinsic quadratic form of the carrier is the Minkowski form of signature
`(1,3)` in the intrinsic frame. -/
theorem lorentz_quadratic_form (x : LorentzCarrier) :
    NS x = x.1 ^ 2 - (x.2 0 ^ 2 + x.2 1 ^ 2 + x.2 2 ^ 2) := by
  simp [NS, sip]
  ring

/-- The intrinsic Lorentz group is the group of real-linear self-equivalences of the
carrier preserving the quadratic form and the cone, with determinant `1`. -/
theorem mem_lorentz_group_iff (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
    F ∈ GLor ↔ ((∀ x, NS (F x) = NS x) ∧ (∀ x, x ∈ ConeS ↔ F x ∈ ConeS)) ∧
      LinearMap.det (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1 := Iff.rfl

/-! ## 2. The Clifford layer -/

/-- The generators of the real Clifford algebra square to `+1` for the Euclidean form. -/
theorem clifford_generator_square (v : Fin 3 → ℝ) :
    CliffordAlgebra.ι q3 v * CliffordAlgebra.ι q3 v = algebraMap ℝ Cl3 (q3 v) :=
  CliffordAlgebra.ι_sq_scalar q3 v

/-- The paravector embedding of the carrier into the Clifford algebra realises the
intrinsic quadratic form: `A(x) · cconj A(x) = N(x)`. -/
theorem paravector_norm (x : LorentzCarrier) :
    spinToCl x * cconj (spinToCl x) = algebraMap ℝ Cl3 (NS x) := spinToCl_norm x

/-! ## 3. The spin group and the double cover -/

/-- **Principal endpoint.**  The intrinsic spin group of `Cl₃(ℝ)` acts on the carrier by
`spinLor`, the action lands in the intrinsic Lorentz group `G_L`, every element of `G_L`
arises this way, and the elements acting trivially are exactly `±1`. -/
theorem spin_double_cover_of_lorentz :
    (∀ {g : Cl3} (hg : IsSpinElem g), spinLorEquiv hg ∈ GLor) ∧
    (∀ F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier, F ∈ GLor →
      ∃ g : Cl3, ∃ hg : IsSpinElem g, spinLorEquiv hg = F) ∧
    (∀ {g : Cl3}, IsSpinElem g → ((∀ x, spinLor g x = x) ↔ g = 1 ∨ g = -1)) :=
  ⟨fun hg => spinLorEquiv_mem_GLor hg,
   fun _ hF => spinLor_surjective_onto_GLor hF,
   fun hg => kernel_exactly_pm_one hg⟩

/-- **Principal endpoint, bundled form.**  The intrinsic spin group is a group, the
Clifford action is a group homomorphism onto the intrinsic Lorentz group, and its kernel is
the central two-element subgroup `{±1}`.  Stated and proved without `SL(2,ℂ)`. -/
theorem spin_double_cover_bundled :
    Function.Surjective spinCover ∧
    (∀ u : SpinGroup, u ∈ spinCover.ker ↔ u = 1 ∨ u = negOneSpin) ∧
    Nat.card (spinCover.ker : Subgroup SpinGroup) = 2 ∧
    (∀ z ∈ spinCover.ker, ∀ u : SpinGroup, z * u = u * z) :=
  ⟨spinCover_surjective, mem_ker_spinCover_iff, spinCover_ker_card,
    fun z hz u => spinCover_ker_central z hz u⟩

/-! ## 4. The topological qualification of the double cover

Re-exported from `RequestProject.Spine.E1.Topology.Core`; see that module for the
construction of the topologies and for the canonicality statements. -/

/-- **Principal endpoint, topological form.**  Both groups are Hausdorff topological
groups, the cover is continuous and surjective, and its kernel is central and discrete. -/
theorem spin_double_cover_topological_endpoint :
    IsTopologicalGroup ↥SpinGroup ∧
    T2Space ↥SpinGroup ∧
    IsTopologicalGroup ↥GLor ∧
    T2Space ↥GLor ∧
    Continuous (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    Function.Surjective (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    (∀ z ∈ spinCover.ker, ∀ u : ↥SpinGroup, z * u = u * z) ∧
    DiscreteTopology (spinCover.ker : Subgroup ↥SpinGroup) ∧
    Nat.card (spinCover.ker : Subgroup ↥SpinGroup) = 2 :=
  spin_double_cover_topological

/-- **Principal endpoint, local form.**  The intrinsic cover admits a continuous local
section around every element of the intrinsic Lorentz group.  Re-exported from
`RequestProject.Spine.E1.Topology.LocalSection`. -/
theorem spin_double_cover_local_section_endpoint :
    ∀ k : GLor, ∃ V : Set GLor, IsOpen V ∧ k ∈ V ∧ ∃ s : GLor → SpinGroup,
      ContinuousOn s V ∧ ∀ y ∈ V, spinCover (s y) = y :=
  intrinsic_spin_cover_hasLocalSection

/-! ## 5. Clifford modules over the carrier -/

/-- **The Clifford-module parameter is inhabited and `ℤ₂`-graded.**  The concrete Weyl
module carries a Clifford action of the carrier which is odd for the chirality involution.
No module is singled out by the algebra: the module remains a parameter. -/
theorem weyl_clifford_module :
    (∀ (x : LorentzCarrier) (s : WeylS), weylAction.act x (weylAction.act x s) = NS x • s) ∧
    (∀ (x : LorentzCarrier) (p : WeylS), weylChi (weylAct x p) = -(weylAct x (weylChi p))) :=
  ⟨weylAction.act_sq, weyl_chirality⟩

end SpinCore

/-! ## Axiom audit of the principal endpoint -/

-- Axiom audit: each of the following must report only `propext`, `Classical.choice`,
-- `Quot.sound`.
#print axioms SpinCore.lorentz_quadratic_form
#print axioms SpinCore.mem_lorentz_group_iff
#print axioms SpinCore.clifford_generator_square
#print axioms SpinCore.paravector_norm
#print axioms SpinCore.spin_double_cover_of_lorentz
#print axioms SpinCore.spin_double_cover_bundled
#print axioms SpinCore.spin_double_cover_topological_endpoint
#print axioms SpinCore.spin_double_cover_local_section_endpoint
#print axioms SpinCore.weyl_clifford_module
