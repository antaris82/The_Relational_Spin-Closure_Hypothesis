import RequestProject.Experiment2.NullSectorTask07.ForcedRelations

/-!
# Task 07, Layer 7: the generated span, its closure, its normal form and its dimension

Only now — after the relations and the independence theorem — is the candidate
span

```
G := span_ℝ {1, A, B, P}
```

introduced.  Closure under the ambient product is **not** assumed; it is proved
from the derived relations alone.  Its dimension is likewise derived: the
ambient carrier `E` keeps an unspecified dimension throughout.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-! ## Normal forms -/

/-- The general real combination of the four derived elements. -/
def gcomb (α β γ δ : ℝ) : E :=
  α • S.oneE + β • S.genA + γ • S.genB + δ • S.genP

/-- The generated span. -/
def Gsub : Submodule ℝ E := Submodule.span ℝ (Set.range S.genFamily)

theorem gcomb_mem (α β γ δ : ℝ) : S.gcomb α β γ δ ∈ S.Gsub := by
  have h1 : S.oneE ∈ S.Gsub := Submodule.subset_span ⟨0, rfl⟩
  have h2 : S.genA ∈ S.Gsub := Submodule.subset_span ⟨1, rfl⟩
  have h3 : S.genB ∈ S.Gsub := Submodule.subset_span ⟨2, rfl⟩
  have h4 : S.genP ∈ S.Gsub := Submodule.subset_span ⟨3, rfl⟩
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2))
    (Submodule.smul_mem _ _ h3)) (Submodule.smul_mem _ _ h4)

/-- **NORMAL FORM (existence).**  Membership in the generated span is exactly
representability as `α•1 + β•A + γ•B + δ•P`. -/
theorem mem_Gsub_iff (x : E) :
    x ∈ S.Gsub ↔ ∃ α β γ δ : ℝ, x = S.gcomb α β γ δ := by
  constructor
  · intro hx
    rw [Gsub, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c 0, c 1, c 2, c 3, ?_⟩
    rw [← hc, Fin.sum_univ_four]
    simp [gcomb]
  · rintro ⟨α, β, γ, δ, rfl⟩
    exact S.gcomb_mem α β γ δ

/-- **NORMAL FORM (uniqueness).**  The four coefficients of an element of the
generated span are unique. -/
theorem gcomb_injective {α β γ δ α' β' γ' δ' : ℝ}
    (h : S.gcomb α β γ δ = S.gcomb α' β' γ' δ') :
    α = α' ∧ β = β' ∧ γ = γ' ∧ δ = δ' := by
  have hz : (α - α') • S.oneE + (β - β') • S.genA + (γ - γ') • S.genB
      + (δ - δ') • S.genP = 0 := by
    simp only [gcomb] at h
    linear_combination (norm := module) h
  obtain ⟨h1, h2, h3, h4⟩ := S.gen_indep_coeffs hz
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## Multiplicative closure -/

/-- **THE FORCED MULTIPLICATION LAW ON NORMAL FORMS.**  Every coefficient is a
consequence of the derived relations and bilinearity; no table was assumed. -/
theorem mul_gcomb (α β γ δ α' β' γ' δ' : ℝ) :
    S.mul (S.gcomb α β γ δ) (S.gcomb α' β' γ' δ') =
      S.gcomb (α * α' + β * β' + γ * γ' - δ * δ')
              (α * β' + β * α' - γ * δ' + δ * γ')
              (α * γ' + β * δ' + γ * α' - δ * β')
              (α * δ' + β * γ' - γ * β' + δ * α') := by
  simp only [gcomb, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    S.one_mul', S.mul_one', S.genA_sq, S.genB_sq, S.genP_sq,
    S.mul_genA_genB, S.mul_genB_genA, S.mul_genA_genP, S.mul_genP_genA,
    S.mul_genB_genP, S.mul_genP_genB]
  module

/-- **CLOSED.**  The generated span is closed under the ambient product. -/
theorem Gsub_mul_closed {x y : E} (hx : x ∈ S.Gsub) (hy : y ∈ S.Gsub) :
    S.mul x y ∈ S.Gsub := by
  obtain ⟨α, β, γ, δ, rfl⟩ := (S.mem_Gsub_iff x).1 hx
  obtain ⟨α', β', γ', δ', rfl⟩ := (S.mem_Gsub_iff y).1 hy
  rw [S.mul_gcomb]
  exact S.gcomb_mem _ _ _ _

/-- The unit lies in the generated span. -/
theorem oneE_mem_Gsub : S.oneE ∈ S.Gsub := Submodule.subset_span ⟨0, rfl⟩

theorem genA_mem_Gsub : S.genA ∈ S.Gsub := Submodule.subset_span ⟨1, rfl⟩
theorem genB_mem_Gsub : S.genB ∈ S.Gsub := Submodule.subset_span ⟨2, rfl⟩
theorem genP_mem_Gsub : S.genP ∈ S.Gsub := Submodule.subset_span ⟨3, rfl⟩

/-! ## Exact dimension -/

/-- **EXACT DIMENSION (DERIVED).**  The generated closure has real dimension
four.  The number `4` was never an input: the ambient space `E` has
unspecified dimension. -/
theorem finrank_Gsub : Module.finrank ℝ S.Gsub = 4 := by
  rw [Gsub, finrank_span_eq_card S.genFamily_linearIndependent]
  simp

/-! ## The derived multiplication table -/

/-- **DERIVED MULTIPLICATION TABLE.**  All sixteen products of the basis
`1, A, B, P`, each one a previously proved theorem or a unit law. -/
theorem multiplication_table :
    (S.mul S.oneE S.oneE = S.oneE ∧ S.mul S.oneE S.genA = S.genA ∧
     S.mul S.oneE S.genB = S.genB ∧ S.mul S.oneE S.genP = S.genP) ∧
    (S.mul S.genA S.oneE = S.genA ∧ S.mul S.genA S.genA = S.oneE ∧
     S.mul S.genA S.genB = S.genP ∧ S.mul S.genA S.genP = S.genB) ∧
    (S.mul S.genB S.oneE = S.genB ∧ S.mul S.genB S.genA = - S.genP ∧
     S.mul S.genB S.genB = S.oneE ∧ S.mul S.genB S.genP = - S.genA) ∧
    (S.mul S.genP S.oneE = S.genP ∧ S.mul S.genP S.genA = - S.genB ∧
     S.mul S.genP S.genB = S.genA ∧ S.mul S.genP S.genP = - S.oneE) :=
  ⟨⟨S.one_mul' _, S.one_mul' _, S.one_mul' _, S.one_mul' _⟩,
   ⟨S.mul_one' _, S.genA_sq, S.mul_genA_genB, S.mul_genA_genP⟩,
   ⟨S.mul_one' _, S.mul_genB_genA, S.genB_sq, S.mul_genB_genP⟩,
   ⟨S.mul_one' _, S.mul_genP_genA, S.mul_genP_genB, S.genP_sq⟩⟩

/-! ## Word reduction -/

/-- **ALGEBRA-GENERATION THEOREM (word reduction).**  The generated span is the
smallest `mul`-closed subspace containing the unit and the two generators;
equivalently, every finite associative word in `A` and `B` reduces to a real
combination of `1, A, B, P`.  (The precise minimality statement is proved in
`Minimality.lean`; here we record that `Gsub` is itself such a subspace.) -/
theorem Gsub_is_closed_subspace :
    S.oneE ∈ S.Gsub ∧ S.genA ∈ S.Gsub ∧ S.genB ∈ S.Gsub ∧
      ∀ x ∈ S.Gsub, ∀ y ∈ S.Gsub, S.mul x y ∈ S.Gsub :=
  ⟨S.oneE_mem_Gsub, S.genA_mem_Gsub, S.genB_mem_Gsub,
    fun _ hx _ hy => S.Gsub_mul_closed hx hy⟩

end AmbientExt

end NullSectorTask07
