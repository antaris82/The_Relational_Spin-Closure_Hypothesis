import RequestProject.Spine.AlgebraicTopology.Contractible
import RequestProject.Spine.AlgebraicTopology.Excision
import RequestProject.Spine.AlgebraicTopology.PairLES

/-!
# Task 19, WP3 : the Mayer–Vietoris comparison for a binary open cover

Given an open cover `X = U ∪ V` with `U` and `V` **contractible**, the Task-18 excision theorem
and the Task-14 long exact sequence of a pair combine into the isomorphisms that the sphere
induction needs.  This is exactly the classical Mayer–Vietoris conclusion for such a cover:
`H_{q+1}(X) ≅ H_q(U ∩ V)` in high degrees, and in degree `1` an identification of `H₁(X)` with
the kernel of `H₀(U ∩ V) → H₀(U)`.

No new short exact sequence is built: the two pair sequences of `(X,V)` and `(U, U∩V)` are the
Task-14 ones, and the comparison between them is the Task-18 `excisionIso`.

* `SpineTask19.mvIsoSucc` — `H_{m+2}(X) ≅ H_{m+1}(U ∩ V)`;
* `SpineTask19.mvIsoOne` — `H₁(X) ≅ H₁(U, U∩V)`;
* `SpineTask19.mv_range_delta_one` — the image of `H₁(U,U∩V) → H₀(U∩V)` is
  `ker (H₀(U∩V) → H₀(U))`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits SpineTask14 SpineTask18

universe u

namespace SpineTask19

variable {X : TopCat.{u}} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hUV : U ∪ V = Set.univ)

/-- The pair map `C_*(V) → C_*(X)`. -/
abbrev incV : TopCat.toSSet.obj (subTop V) ⟶ TopCat.toSSet.obj X :=
  TopCat.toSSet.map (subInc V)

/-- The pair map `C_*(U ∩ V) → C_*(U)`. -/
abbrev incUW : TopCat.toSSet.obj (subTop (U ∩ V)) ⟶ TopCat.toSSet.obj (subTop U) :=
  TopCat.toSSet.map (incInterU U V)

theorem incV_injective (n) : Function.Injective ((incV V).app n) :=
  toSSet_map_injective _ (subInc_injective V) n

theorem incUW_injective (n) : Function.Injective ((incUW U V).app n) :=
  toSSet_map_injective _ (incInterU_injective U V) n

section Contractible

variable [ContractibleSpace ↥U] [ContractibleSpace ↥V]

include hU hV hUV

/-- **WP3.**  `H_{m+2}(X) ≅ H_{m+1}(U ∩ V)` for a cover by two contractible open sets. -/
def mvIsoSucc (m : ℕ) :
    (singCx X).homology (m + 2) ≅ (singCx (subTop (U ∩ V))).homology (m + 1) :=
  haveI : IsIso (pProj (incV V) (m + 2)) :=
    isIso_pProj (incV V) (incV_injective V) (m + 1)
      (isZero_homology_of_contractible (X := subTop V) (m + 1))
      (isZero_homology_of_contractible (X := subTop V) m)
  haveI : IsIso (pairDelta (incUW U V) (incUW_injective U V) (m + 1)) :=
    isIso_pairDelta (incUW U V) (incUW_injective U V) (m + 1)
      (isZero_homology_of_contractible (X := subTop U) (m + 1))
      (isZero_homology_of_contractible (X := subTop U) m)
  asIso (pProj (incV V) (m + 2)) ≪≫ (excisionIso U V hU hV hUV (m + 2)).symm
    ≪≫ asIso (pairDelta (incUW U V) (incUW_injective U V) (m + 1))

/-- **WP3, degree one.**  `H₁(X) ≅ H₁(U, U ∩ V)`, provided `H₀(V) → H₀(X)` is injective. -/
def mvIsoOne (hm : Mono (pIota (incV V) 0)) :
    (singCx X).homology 1 ≅ relHomology (incUW U V) 1 :=
  haveI : IsIso (pProj (incV V) 1) :=
    isIso_pProj_one (incV V) (incV_injective V)
      (isZero_homology_of_contractible (X := subTop V) 0) hm
  asIso (pProj (incV V) 1) ≪≫ (excisionIso U V hU hV hUV 1).symm

end Contractible

section DegreeOne

variable [ContractibleSpace ↥U]

/-- The connecting map `H₁(U, U∩V) → H₀(U∩V)` is injective. -/
theorem mv_mono_delta_one : Mono (pairDelta (incUW U V) (incUW_injective U V) 0) :=
  mono_pairDelta (incUW U V) (incUW_injective U V) 0
    (isZero_homology_of_contractible (X := subTop U) 0)

omit [ContractibleSpace ↥U] in
/-- Its image is the kernel of `H₀(U∩V) → H₀(U)`. -/
theorem mv_range_delta_one :
    LinearMap.range ((pairDelta (incUW U V) (incUW_injective U V) 0).hom)
      = LinearMap.ker ((pIota (incUW U V) 0).hom) :=
  range_pairDelta (incUW U V) (incUW_injective U V) 0

end DegreeOne

end SpineTask19
