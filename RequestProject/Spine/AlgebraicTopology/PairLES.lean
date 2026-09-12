import RequestProject.Spine.AlgebraicTopology.RelativeLES

/-!
# Task 19, WP1 : usable consequences of the Task-14 long exact sequence of a pair

Task 14 supplies the three exactness statements `pair_exact₁/₂/₃` and the connecting map
`pairDelta`.  This module extracts the four consequences that the sphere computation needs:

* `SpineTask19.isIso_pProj` — `H_q(T) ≅ H_q(T,S)` when `H_q(S) = H_{q-1}(S) = 0`;
* `SpineTask19.isIso_pProj_one` — the same in degree `1`, where instead of `H₀(S) = 0` one only
  assumes that `H₀(S) → H₀(T)` is injective;
* `SpineTask19.isIso_pairDelta` — `∂ : H_{q+1}(T,S) ≅ H_q(S)` when `H_{q+1}(T) = H_q(T) = 0`;
* `SpineTask19.range_pairDelta` — the image of `∂` is the kernel of `H_q(S) → H_q(T)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits SpineTask14

universe u

namespace SpineTask19

variable {S T : SSet.{u}} (f : S ⟶ T) (hf : ∀ n, Function.Injective (f.app n))

/-- `H_q(S) → H_q(T)`. -/
abbrev pIota (q : ℕ) : sSetHomology S q ⟶ sSetHomology T q :=
  HomologicalComplex.homologyMap (sSetChainComplexFunctor.map f) q

/-- `H_q(T) → H_q(T,S)`. -/
abbrev pProj (q : ℕ) : sSetHomology T q ⟶ relHomology f q :=
  HomologicalComplex.homologyMap (relProj f) q

include hf

/-- `H_q(T) ≅ H_q(T,S)` as soon as `H_q(S)` and `H_{q-1}(S)` vanish. -/
theorem isIso_pProj (q : ℕ) (h1 : IsZero (sSetHomology S (q + 1)))
    (h0 : IsZero (sSetHomology S q)) : IsIso (pProj f (q + 1)) := by
  have hmono : Mono (pProj f (q + 1)) :=
    (pair_exact₂ f hf (q + 1)).mono_g (h1.eq_zero_of_src _)
  have hepi : Epi (pProj f (q + 1)) :=
    (pair_exact₃ f hf q).epi_f (h0.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- `∂ : H_{q+1}(T,S) ≅ H_q(S)` as soon as `H_{q+1}(T)` and `H_q(T)` vanish. -/
theorem isIso_pairDelta (q : ℕ) (h1 : IsZero (sSetHomology T (q + 1)))
    (h0 : IsZero (sSetHomology T q)) : IsIso (pairDelta f hf q) := by
  have hmono : Mono (pairDelta f hf q) :=
    (pair_exact₃ f hf q).mono_g (h1.eq_zero_of_src _)
  have hepi : Epi (pairDelta f hf q) :=
    (pair_exact₁ f hf q).epi_f (h0.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The connecting map is mono once `H_{q+1}(T)` vanishes. -/
theorem mono_pairDelta (q : ℕ) (h1 : IsZero (sSetHomology T (q + 1))) :
    Mono (pairDelta f hf q) :=
  (pair_exact₃ f hf q).mono_g (h1.eq_zero_of_src _)

/-- The image of the connecting map is the kernel of `H_q(S) → H_q(T)`. -/
theorem range_pairDelta (q : ℕ) :
    LinearMap.range ((pairDelta f hf q).hom) = LinearMap.ker ((pIota f q).hom) :=
  (pair_exact₁ f hf q).moduleCat_range_eq_ker

/-- In degree `1` it is enough that `H₀(S) → H₀(T)` be a monomorphism. -/
theorem isIso_pProj_one (h1 : IsZero (sSetHomology S 1)) (hm : Mono (pIota f 0)) :
    IsIso (pProj f 1) := by
  have hmono : Mono (pProj f 1) := (pair_exact₂ f hf 1).mono_g (h1.eq_zero_of_src _)
  have hdz : pairDelta f hf 0 = 0 := by
    have hz := (relSC_shortExact f hf).δ_comp 1 0 (by simp)
    exact zero_of_comp_mono (pIota f 0) hz
  have hepi : Epi (pProj f 1) := (pair_exact₃ f hf 0).epi_f hdz
  exact isIso_of_mono_of_epi _

end SpineTask19
