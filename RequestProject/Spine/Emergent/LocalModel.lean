import RequestProject.Spine.E1.SpinCover

/-!
# Spine / Emergent : the base-free local model of the Clifford–Spin core

**First module of the manifold-emergence layer (Task 32, §6 "local model gate").**

The question this module answers is the *local model gate*:

> does the already certified local Clifford/Spin core supply, with no manifold and no base
> space anywhere in sight, a canonical four-dimensional real local model carrying the
> Lorentz structure?

The answer is yes, and nothing new has to be built: the intrinsic carrier
`SpinCore.LorentzCarrier = ℝ ⊕ ℝ³` of the E1 core *is* that model.  This module only

* names it `EmergentBase.LocalModel`, so that later modules can speak of "the local model"
  without repeating the provenance;
* records that it is a four-dimensional real topological vector space
  (`EmergentBase.finrank_localModel`, `EmergentBase.localModelEquivFin4`);
* records that the Lorentz representation of the Spin core acts on it by linear
  automorphisms preserving the intrinsic Lorentz quadratic form `SpinCore.NS`
  (`EmergentBase.spin_acts_on_localModel`).

## What is deliberately *not* claimed

`LocalModel` is **not** called a tangent space, and no manifold, chart, atlas, base point or
cover occurs here or in the import closure of this module: the closure consists of `Mathlib`
and modules of `RequestProject.Spine.E1` only.  The model is a *candidate* local model for
every future chart, and nothing more.  Whether local copies of it can be glued into a base
is the subject of `RequestProject.Spine.Emergent.BaseGluing`, and the answer there is
negative for the Spin data alone.
-/

noncomputable section

namespace EmergentBase

open SpinCore

/-- **EXPOSED, not newly defined (Task 32).**  The canonical base-free local model supplied
by the Clifford–Spin core: the intrinsic real carrier `𝒮 = ℝ ⊕ ℝ³` of the E1 core, with its
product topology and its intrinsic Lorentz quadratic form `SpinCore.NS`.

It is *not* a tangent space and there is no manifold in scope. -/
abbrev LocalModel : Type := SpinCore.LorentzCarrier

/-- The local model is linearly isomorphic to `ℝ⁴`; this is the inherited intrinsic
coordinate equivalence of the core, not a new choice. -/
def localModelEquivFin4 : LocalModel ≃ₗ[ℝ] (Fin 4 → ℝ) := SpinCore.spinToVec

/-- **The local model is four-dimensional.** -/
theorem finrank_localModel : Module.finrank ℝ LocalModel = 4 := by
  rw [localModelEquivFin4.finrank_eq, Module.finrank_fin_fun]

/-- The local model is a real topological vector space: addition and scalar multiplication
are continuous.  (Both are instances; the statement records that they are available.) -/
theorem localModel_topologicalVectorSpace :
    ContinuousAdd LocalModel ∧ ContinuousSMul ℝ LocalModel :=
  ⟨inferInstance, inferInstance⟩

/-- **The Lorentz representation of the Spin core acts on the local model.**  Every element
of the intrinsic Spin group acts on `LocalModel` through the certified double cover
`SpinCore.spinCover` by a real-linear automorphism which preserves the intrinsic Lorentz
quadratic form `NS`, preserves the intrinsic cone, and has determinant one.

This is the arrow *local Clifford/Spin core → Lorentz representation → 4-dimensional real
local model* of the Task-32 DAG.  No base point, chart or manifold occurs in it. -/
theorem spin_acts_on_localModel (g : SpinCore.SpinGroup) :
    (∀ x : LocalModel,
        NS ((SpinCore.spinCover g : LocalModel ≃ₗ[ℝ] LocalModel) x) = NS x) ∧
    (∀ x : LocalModel,
        x ∈ ConeS ↔ (SpinCore.spinCover g : LocalModel ≃ₗ[ℝ] LocalModel) x ∈ ConeS) ∧
    LinearMap.det
      ((SpinCore.spinCover g : LocalModel ≃ₗ[ℝ] LocalModel) : LocalModel →ₗ[ℝ] LocalModel)
      = 1 :=
  ⟨(SpinCore.spinCover g).2.1.1, (SpinCore.spinCover g).2.1.2, (SpinCore.spinCover g).2.2⟩

end EmergentBase
