import RequestProject.Experiment2.NullSectorTask07.GeneratedClosure

/-!
# Task 07, Layer 8: minimality of the generated closure

Every real-linear subspace of the ambient extension that contains the unit and
the two inherited spatial generators and is closed under the ambient product
already contains the whole derived four-dimensional closure.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-- A subspace containing the unit and the two generators and closed under the
ambient product. -/
structure IsGenClosed (H : Submodule ℝ E) : Prop where
  one_mem : S.oneE ∈ H
  genA_mem : S.genA ∈ H
  genB_mem : S.genB ∈ H
  mul_mem : ∀ x ∈ H, ∀ y ∈ H, S.mul x y ∈ H

/-- **MINIMAL (step 1).**  Any such subspace already contains the mixed
product. -/
theorem genP_mem_of_isGenClosed {H : Submodule ℝ E} (hH : S.IsGenClosed H) :
    S.genP ∈ H :=
  hH.mul_mem _ hH.genA_mem _ hH.genB_mem

/-- **MINIMAL.**  Any such subspace contains the entire generated closure. -/
theorem Gsub_le_of_isGenClosed {H : Submodule ℝ E} (hH : S.IsGenClosed H) :
    S.Gsub ≤ H := by
  rw [Gsub, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact hH.one_mem
  · exact hH.genA_mem
  · exact hH.genB_mem
  · exact S.genP_mem_of_isGenClosed hH

/-- The generated closure is itself product-closed and contains the
generators. -/
theorem isGenClosed_Gsub : S.IsGenClosed S.Gsub :=
  ⟨S.oneE_mem_Gsub, S.genA_mem_Gsub, S.genB_mem_Gsub,
    fun _ hx _ hy => S.Gsub_mul_closed hx hy⟩

/-- **MINIMALITY THEOREM.**  `Gsub` is the smallest product-closed subspace
containing the unit and the two inherited spatial generators. -/
theorem Gsub_least :
    S.IsGenClosed S.Gsub ∧ ∀ H : Submodule ℝ E, S.IsGenClosed H → S.Gsub ≤ H :=
  ⟨S.isGenClosed_Gsub, fun _ hH => S.Gsub_le_of_isGenClosed hH⟩

/-- **WORD REDUCTION (equivalent generation statement).**  Every element
obtainable from `1, A, B` by real linear combinations and finitely many ambient
products lies in the span of `1, A, B, P`: indeed the span of `1, A, B, P` is
contained in every product-closed subspace containing `1, A, B`, and is itself
one. -/
theorem word_reduction (H : Submodule ℝ E) (hH : S.IsGenClosed H) :
    S.Gsub ≤ H ∧ ∀ x ∈ S.Gsub, ∃ α β γ δ : ℝ, x = S.gcomb α β γ δ :=
  ⟨S.Gsub_le_of_isGenClosed hH, fun x hx => (S.mem_Gsub_iff x).1 hx⟩

end AmbientExt

end NullSectorTask07
