import Mathlib
import RequestProject.Spine.E1.Topology.SpinTopology
import RequestProject.Spine.E1.Topology.LorentzTopology
import RequestProject.Spine.E1.SpinKernel

/-!
# Spine / E1 / Topology : continuity of the intrinsic spin cover and discreteness of its kernel

This module closes the topological qualification of the intrinsic algebraic double cover
`SpinCore.spinCover : SpinGroup →* GLor`.  Nothing here is transported from the downstream
`SL(2,ℂ)` comparison: the continuity proof runs through the actual definition of the cover.

## The continuity chain (WP4)

`spinCover u` is the linear automorphism induced by the twisted Clifford action
`spinAct g x = g · A(x) · reverse g` (with `A = SpinCore.spinToCl` the embedding of the
carrier into `Cl₃(ℝ)`).  The action is defined through a choice
(`SpinCore.spinLor g x` is *the* carrier element with `A (spinLor g x) = spinAct g x`), so
continuity cannot be read off the definition syntactically.  It is obtained instead from a
*linear retraction* of the embedding:

* `SpinCore.spinToClLin` — the embedding `A` as an `ℝ`-linear map (its injectivity is the
  already proved `SpinCore.spinToCl_injective`);
* `SpinCore.paraRetract` — a linear left inverse of `A`, which exists because `A` is an
  injective linear map of finite-dimensional real vector spaces;
* `SpinCore.spinLor_eq_paraRetract` — hence `spinLor g x = paraRetract (g · A x · reverse g)`,
  an expression built only from multiplication in `Cl₃(ℝ)`, reversion, and linear maps;
* `SpinCore.continuous_spinLor_apply`, `SpinCore.continuous_spinLorLin` — so the Clifford
  action `Cl₃(ℝ) → End(𝒮)` is continuous, by continuity of the ring multiplication
  (`IsTopologicalRing Cl3`), of the linear map `reverse`, and of `paraRetract`, together
  with the basis evaluation criterion `SpineTop.continuous_into_linearMap`;
* `SpinCore.continuous_spinCover` — and therefore the cover itself is continuous, because
  the topology of the target is induced from `End(𝒮) × End(𝒮)ᵐᵒᵖ` by `F ↦ (F, F⁻¹)`, and
  the inverse of `spinCover u` is the action of the Clifford conjugate `cconj u`.

## Discreteness of the kernel (WP5)

The kernel is *not* declared discrete because it is small: discreteness is derived from the
separation property of the source.  `SpinGroup` is Hausdorff (inherited from `Cl₃(ℝ)`), the
kernel carries the subspace topology, and the already proved
`SpinCore.spinCover_ker_card : Nat.card (ker spinCover) = 2` makes it finite; a finite
Hausdorff space is discrete.

## The theorem package

`SpinCore.TopologicalCentralCover` is a small native record containing exactly the
properties established here: a continuous surjective homomorphism of Hausdorff topological
groups with central, discrete, two-element kernel.  It is deliberately *not* the `E2`
interface `InternalProjection`, which additionally demands continuous local sections — an
obligation this task does not address.  `SpinCore.topologicalSpinProjection` is the
intrinsic instance.

**Import firewall.**  `Mathlib`, the three topology modules of this layer and the intrinsic
spin core.  No `SL(2,ℂ)`, no matrix model, no `RequestProject.Spine.E2`, no historical
experiment module.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-! ## The paravector embedding and a linear retraction -/

/-- The embedding of the carrier into the Clifford algebra, as an `ℝ`-linear map. -/
def spinToClLin : LorentzCarrier →ₗ[ℝ] Cl3 where
  toFun := spinToCl
  map_add' := spinToCl_add
  map_smul' := spinToCl_smul

@[simp] theorem spinToClLin_apply (x : LorentzCarrier) : spinToClLin x = spinToCl x := rfl

theorem spinToClLin_ker : LinearMap.ker spinToClLin = ⊥ :=
  LinearMap.ker_eq_bot.2 spinToCl_injective

/-- A linear left inverse of the paravector embedding.  It exists because the embedding is
an injective linear map of finite-dimensional real vector spaces; only its existence, not a
particular choice, is used below. -/
def paraRetract : Cl3 →ₗ[ℝ] LorentzCarrier :=
  (LinearMap.exists_leftInverse_of_injective spinToClLin spinToClLin_ker).choose

@[simp] theorem paraRetract_spinToCl (x : LorentzCarrier) : paraRetract (spinToCl x) = x := by
  have h := (LinearMap.exists_leftInverse_of_injective spinToClLin spinToClLin_ker).choose_spec
  simpa using LinearMap.congr_fun h x

/-- **The action in retracted form.**  The induced map on the carrier is the retraction of
the twisted Clifford product; this is the representation that exhibits it as continuous. -/
theorem spinLor_eq_paraRetract (g : Cl3) (x : LorentzCarrier) :
    spinLor g x = paraRetract (g * spinToCl x * reverse (Q := q3) g) := by
  have h : paraRetract (spinToCl (spinLor g x)) = spinLor g x := paraRetract_spinToCl _
  rw [spinToCl_spinLor] at h
  exact h.symm

/-! ## Continuity of the Clifford action -/

/-- For a fixed carrier vector, the induced action depends continuously on the Clifford
element: it is a retraction of a product of continuous maps. -/
theorem continuous_spinLor_apply (x : LorentzCarrier) :
    Continuous fun g : Cl3 => spinLor g x := by
  have hmul : Continuous fun g : Cl3 => g * spinToCl x * reverse (Q := q3) g :=
    (continuous_id.mul continuous_const).mul continuous_reverse
  have h2 := (continuous_linearMap_Cl3 paraRetract).comp hmul
  have heq : (fun g : Cl3 => spinLor g x)
      = (⇑paraRetract ∘ fun g : Cl3 => g * spinToCl x * reverse (Q := q3) g) := by
    funext g
    exact spinLor_eq_paraRetract g x
  rw [heq]
  exact h2

/-- The basis of the carrier coming from its intrinsic real coordinates. -/
def carrierBasis : Module.Basis (Fin 4) ℝ LorentzCarrier := Module.Basis.ofEquivFun spinToVec

/-- **The Clifford action is continuous as a map into the endomorphism algebra of the
carrier.**  This is the analytic core of WP4. -/
theorem continuous_spinLorLin : Continuous fun g : Cl3 => (spinLorLin g : EndLor) := by
  refine SpineTop.continuous_into_linearMap carrierBasis _ fun i => ?_
  simpa using continuous_spinLor_apply (carrierBasis i)

/-! ## Continuity of the spin cover -/

theorem continuous_spinCover_toLinearMap :
    Continuous fun u : ↥SpinGroup =>
      ((spinCover u : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier).toLinearMap := by
  have h : (fun u : ↥SpinGroup =>
      ((spinCover u : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier).toLinearMap)
      = fun u : ↥SpinGroup => spinLorLin (((u : Cl3ˣ) : Cl3)) := by
    funext u
    rfl
  rw [h]
  exact continuous_spinLorLin.comp continuous_spinGroup_val

theorem continuous_spinCover_symm_toLinearMap :
    Continuous fun u : ↥SpinGroup =>
      ((spinCover u : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier).symm.toLinearMap := by
  have h : (fun u : ↥SpinGroup =>
      ((spinCover u : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier).symm.toLinearMap)
      = fun u : ↥SpinGroup => spinLorLin (cconj ((u : Cl3ˣ) : Cl3)) := by
    funext u
    rfl
  rw [h]
  exact continuous_spinLorLin.comp continuous_spinGroup_cconj

/-- **WP4.  The intrinsic spin cover is continuous.**  The proof uses the definition of
`spinCover` — the twisted Clifford action — and reduces it to multiplication in `Cl₃(ℝ)`,
Clifford reversion and conjugation, and finite-dimensional linear maps.  It does not use
the `SL(2,ℂ)` comparison. -/
theorem continuous_spinCover : Continuous (⇑spinCover : ↥SpinGroup → ↥GLor) := by
  refine continuous_induced_rng.2 ?_
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_spinCover_toLinearMap
  · exact continuous_spinCover_symm_toLinearMap

/-! ## Discreteness of the kernel -/

instance instFiniteSpinCoverKer : Finite (spinCover.ker : Subgroup ↥SpinGroup) :=
  Nat.finite_of_card_ne_zero (by rw [spinCover_ker_card]; norm_num)

/-- **WP5.  The kernel of the intrinsic spin cover is discrete.**  Not because it has two
elements, but because the source is Hausdorff and the kernel carries the subspace topology:
a finite Hausdorff space is discrete. -/
instance instDiscreteTopologySpinCoverKer :
    DiscreteTopology (spinCover.ker : Subgroup ↥SpinGroup) := inferInstance

/-! ## The theorem package -/

/-- A **continuous central cover**: a continuous surjective homomorphism of Hausdorff
topological groups whose kernel is central and discrete.  This records exactly the
properties proved in this task.  It is deliberately weaker than the generic `E2` interface
`InternalProjection`, which also requires continuous local sections. -/
structure TopologicalCentralCover (L G : Type*) [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [T2Space L] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] where
  /-- The projection, as a group homomorphism. -/
  proj : L →* G
  /-- The projection is continuous. -/
  continuous_proj : Continuous proj
  /-- The projection is surjective. -/
  surjective_proj : Function.Surjective proj
  /-- The kernel is central. -/
  ker_central : ∀ z ∈ proj.ker, ∀ l : L, z * l = l * z
  /-- The kernel is discrete in the inherited subgroup topology. -/
  ker_discrete : DiscreteTopology (proj.ker : Subgroup L)
  /-- The kernel has exactly two elements. -/
  ker_card : Nat.card (proj.ker : Subgroup L) = 2

/-- **The intrinsic topological spin projection.**  The algebraic double cover of
`RequestProject.Spine.E1.SpinKernel`, qualified topologically: `SpinGroup` and `GLor` are
Hausdorff topological groups (with topologies inherited canonically from the
finite-dimensional real Clifford algebra and from the endomorphism algebra of the carrier
respectively), `spinCover` is continuous and surjective, and its kernel `{±1}` is central
and discrete. -/
def topologicalSpinProjection :
    TopologicalCentralCover ↥SpinGroup ↥GLor where
  proj := spinCover
  continuous_proj := continuous_spinCover
  surjective_proj := spinCover_surjective
  ker_central := spinCover_ker_central
  ker_discrete := instDiscreteTopologySpinCoverKer
  ker_card := spinCover_ker_card

/-- **The endpoint of Task 1, unbundled.**  The intrinsic algebraic Spin/Lorentz double
cover carries natural topological-group structures for which the cover is a continuous
surjective homomorphism with central discrete two-element kernel. -/
theorem intrinsic_spin_cover_topological :
    IsTopologicalGroup ↥SpinGroup ∧
    T2Space ↥SpinGroup ∧
    IsTopologicalGroup (GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)) ∧
    T2Space (GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)) ∧
    Continuous (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    Function.Surjective (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    (∀ z ∈ spinCover.ker, ∀ u : ↥SpinGroup, z * u = u * z) ∧
    DiscreteTopology (spinCover.ker : Subgroup ↥SpinGroup) ∧
    Nat.card (spinCover.ker : Subgroup ↥SpinGroup) = 2 :=
  ⟨instIsTopologicalGroupSpinGroup, instT2SpaceSpinGroup, instIsTopologicalGroupGLor,
    instT2SpaceGLor, continuous_spinCover, spinCover_surjective,
    fun z hz u => spinCover_ker_central z hz u, instDiscreteTopologySpinCoverKer,
    spinCover_ker_card⟩

end SpinCore

/-! ## Axiom audit of the topological spin layer

Each of the following must report only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms SpinCore.instTopologicalSpaceCl3
#print axioms SpinCore.instIsTopologicalRingCl3
#print axioms SpinCore.instT2SpaceCl3
#print axioms SpinCore.Cl3_topology_unique
#print axioms SpinCore.instIsTopologicalRingEndLor
#print axioms SpinCore.EndLor_topology_unique
#print axioms SpinCore.instIsTopologicalGroupGLor
#print axioms SpinCore.instIsTopologicalGroupSpinGroup
#print axioms SpinCore.continuous_spinLorLin
#print axioms SpinCore.continuous_spinCover
#print axioms SpinCore.instDiscreteTopologySpinCoverKer
#print axioms SpinCore.topologicalSpinProjection
#print axioms SpinCore.intrinsic_spin_cover_topological
