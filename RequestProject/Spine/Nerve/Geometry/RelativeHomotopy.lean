import RequestProject.Spine.Nerve.Geometry.PushoutRetraction
import RequestProject.Spine.AlgebraicTopology.RelativeAcyclicity
import RequestProject.Spine.AlgebraicTopology.SingularHomotopy

/-!
# Task 23, WP4 — the relative consequence of the deformation retraction

Task 23 WP3 produced a deformation retraction of `V = |Sk X (r+1)| \ B` onto `A = |Sk X r|`
fixing `A` pointwise.  This module packages the *relative* consequence needed by the excision
step:

* `vHomotopyEquiv` — the inclusion `A ↪ V` is a homotopy equivalence;
* `isZero_relHomology_of_quasiIso` — a general lemma: if `C_*(S) → C_*(T)` is a quasi-isomorphism
  (and `f` is degreewise injective) then the relative complex `C_*(T,S)` is acyclic;
* `isZero_relHomology_skToV` — **`H_q^{sing}(V, A; ℤ₂) = 0` for every `q`**.

Only the existing Task-14 relative chain machinery and the existing Task-18/Task-19 homotopy
invariance are used; no new theory of relative homotopy equivalences is built.
-/

noncomputable section

open CategoryTheory Limits Simplicial SSet NerveGeom SpineTask13 SpineTask14 SpineTask15
  SpineTask19

universe u

namespace SpineTask23

section Skeleton

variable (X : SSet.{u}) (r : ℕ)

/-- The inclusion `A = |Sk X r| ⟶ V`, as a morphism of `TopCat`. -/
def skToVMap : SSet.toTop.{u}.obj (Sk X r) ⟶ TopCat.of ↥(puncturedNbhd X r) :=
  TopCat.ofHom (skToV X r)

theorem skToV_injective : Function.Injective (skToV X r) := by
  intro x y h
  exact skInc_injective X r (congrArg Subtype.val h)

/-- The homotopy `id_V ≃ skToV ∘ vRetract` produced by WP3. -/
def vHomotopyStruct : (ContinuousMap.id ↥(puncturedNbhd X r)).Homotopy
    ((skToV X r).comp (vRetract X r)) where
  toFun := vHomotopy X r
  continuous_toFun := (vHomotopy X r).continuous
  map_zero_left := vHomotopy_zero X r
  map_one_left := vHomotopy_one X r

/-- **The inclusion `A ↪ V` is a homotopy equivalence.** -/
def vHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥(SSet.toTop.{u}.obj (Sk X r)) ↥(puncturedNbhd X r) where
  toFun := skToV X r
  invFun := vRetract X r
  left_inv := by
    have h : (vRetract X r).comp (skToV X r) = ContinuousMap.id _ :=
      ContinuousMap.ext (vRetract_skToV X r)
    rw [h]
  right_inv := ⟨(vHomotopyStruct X r).symm⟩

/-- The inclusion induces isomorphisms on singular homology. -/
theorem isIso_homologyMap_skToV (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (TopCat.toSSet.map (skToVMap X r))) q) := by
  have h := isIso_homologyMap_of_homotopyEquiv (X := SSet.toTop.obj (Sk X r))
    (Y := TopCat.of ↥(puncturedNbhd X r)) (vHomotopyEquiv X r) q
  exact h

/-- **WP4.  `H_q^{sing}(V, A; ℤ₂) = 0` for every `q`.** -/
theorem isZero_relHomology_skToV (q : ℕ) :
    IsZero ((relChainCx (TopCat.toSSet.map (skToVMap X r))).homology q) :=
  isZero_relHomology_of_quasiIso _
    (toSSet_map_injective _ (skToV_injective X r))
    (isIso_homologyMap_skToV X r) q

end Skeleton

end SpineTask23
