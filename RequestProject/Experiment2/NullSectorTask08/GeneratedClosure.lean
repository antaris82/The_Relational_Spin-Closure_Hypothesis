import RequestProject.Experiment2.NullSectorTask08.Independence

/-!
# Task 08, Layer 7: the generated span, its closure, its normal form and its dimension

Only now — after all relations, the membership classification and the
independence audit — is the candidate span

```
G₃ := span_ℝ {1, A, B, C, P, Q, R, S₃}
```

introduced.  No listed element is redundant (Layer 6), so the span is formed on
the independently established minimal family.  Multiplicative closure is not
assumed; it is derived from the relation ledger alone, and the exact dimension
is an output.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-- **THE GENERATED SPAN.** -/
def G3 : Submodule ℝ E := Submodule.span ℝ (Set.range (genFamily8 S))

theorem comb8_mem (a0 a1 a2 a3 a4 a5 a6 a7 : ℝ) :
    comb8 S a0 a1 a2 a3 a4 a5 a6 a7 ∈ G3 S := by
  have h : ∀ i : Fin 8, genFamily8 S i ∈ G3 S := fun i => Submodule.subset_span ⟨i, rfl⟩
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [genFamily8_zero, genFamily8_one, genFamily8_two, genFamily8_three,
    genFamily8_four, genFamily8_five, genFamily8_six, genFamily8_seven] at h0 h1 h2 h3 h4 h5 h6 h7
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1))
      (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3))
      (Submodule.smul_mem _ _ h4)) (Submodule.smul_mem _ _ h5))
      (Submodule.smul_mem _ _ h6)) (Submodule.smul_mem _ _ h7)

theorem oneE_mem_G3 : S.oneE ∈ G3 S := Submodule.subset_span ⟨0, rfl⟩
theorem genA_mem_G3 : S.genA ∈ G3 S := Submodule.subset_span ⟨1, rfl⟩
theorem genB_mem_G3 : S.genB ∈ G3 S := Submodule.subset_span ⟨2, rfl⟩
theorem genC_mem_G3 : genC S ∈ G3 S := Submodule.subset_span ⟨3, rfl⟩
theorem genP_mem_G3 : S.genP ∈ G3 S := Submodule.subset_span ⟨4, rfl⟩
theorem genQ_mem_G3 : genQ S ∈ G3 S := Submodule.subset_span ⟨5, rfl⟩
theorem genR_mem_G3 : genR S ∈ G3 S := Submodule.subset_span ⟨6, rfl⟩
theorem genS_mem_G3 : genS S ∈ G3 S := Submodule.subset_span ⟨7, rfl⟩

/-! ## Normal form -/

/-- **NORMAL FORM (existence).**  Membership in the generated span is exactly
representability by eight real coefficients. -/
theorem mem_G3_iff (x : E) :
    x ∈ G3 S ↔ ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ℝ, x = comb8 S a0 a1 a2 a3 a4 a5 a6 a7 := by
  constructor
  · intro hx
    rw [G3, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, ?_⟩
    rw [← hc, Fin.sum_univ_eight]
    simp [comb8]
  · rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
    exact comb8_mem S a0 a1 a2 a3 a4 a5 a6 a7

/-- **NORMAL FORM (uniqueness).**  The eight coefficients of an element of the
generated span are unique. -/
theorem comb8_injective {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℝ}
    (h : comb8 S a0 a1 a2 a3 a4 a5 a6 a7 = comb8 S b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  have hz : comb8 S (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) (a4 - b4) (a5 - b5)
      (a6 - b6) (a7 - b7) = 0 := by
    simp only [comb8] at h ⊢
    linear_combination (norm := module) h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := comb8_eq_zero_iff S hz
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-! ## The forced multiplication law on normal forms -/

/-- **THE FORCED COEFFICIENT LAW.**  Every coefficient below is a consequence of
the derived relation ledger and bilinearity; no multiplication table was
assumed. -/
theorem mul_comb8 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℝ) :
    S.mul (comb8 S a0 a1 a2 a3 a4 a5 a6 a7) (comb8 S b0 b1 b2 b3 b4 b5 b6 b7) =
      comb8 S
        (a0*b0 + a1*b1 + a2*b2 + a3*b3 - a4*b4 - a5*b5 - a6*b6 - a7*b7)
        (a0*b1 + a1*b0 - a2*b4 - a3*b5 + a4*b2 + a5*b3 - a6*b7 - a7*b6)
        (a0*b2 + a1*b4 + a2*b0 - a3*b6 - a4*b1 + a5*b7 + a6*b3 + a7*b5)
        (a0*b3 + a1*b5 + a2*b6 + a3*b0 - a4*b7 - a5*b1 - a6*b2 - a7*b4)
        (a0*b4 + a1*b2 - a2*b1 + a3*b7 + a4*b0 - a5*b6 + a6*b5 + a7*b3)
        (a0*b5 + a1*b3 - a2*b7 - a3*b1 + a4*b6 + a5*b0 - a6*b4 - a7*b2)
        (a0*b6 + a1*b7 + a2*b3 - a3*b2 - a4*b5 + a5*b4 + a6*b0 + a7*b1)
        (a0*b7 + a1*b6 - a2*b5 + a3*b4 + a4*b3 - a5*b2 + a6*b1 + a7*b0) := by
  simp only [comb8, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    S.one_mul', S.mul_one',
    S.genA_sq, S.mul_genA_genB, mul_genA_genC, S.mul_genA_genP, mul_genA_genQ,
    mul_genA_genR, mul_genA_genS,
    S.mul_genB_genA, S.genB_sq, mul_genB_genC, S.mul_genB_genP, mul_genB_genQ,
    mul_genB_genR, mul_genB_genS,
    mul_genC_genA, mul_genC_genB, genC_sq, mul_genC_genP, mul_genC_genQ,
    mul_genC_genR, mul_genC_genS,
    S.mul_genP_genA, S.mul_genP_genB, mul_genP_genC, S.genP_sq, mul_genP_genQ,
    mul_genP_genR, mul_genP_genS,
    mul_genQ_genA, genQ_mul_genB, mul_genQ_genC, mul_genQ_genP, genQ_sq,
    mul_genQ_genR, mul_genQ_genS,
    mul_genR_genA, mul_genR_genB, mul_genR_genC, mul_genR_genP, mul_genR_genQ,
    genR_sq, mul_genR_genS,
    mul_genS_genA, mul_genS_genB, mul_genS_genC, mul_genS_genP, mul_genS_genQ,
    mul_genS_genR, genS_sq]
  module

/-- **CLOSED.**  The generated span is closed under the ambient product. -/
theorem G3_mul_closed {x y : E} (hx : x ∈ G3 S) (hy : y ∈ G3 S) : S.mul x y ∈ G3 S := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := (mem_G3_iff S x).1 hx
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := (mem_G3_iff S y).1 hy
  rw [mul_comb8]
  exact comb8_mem S _ _ _ _ _ _ _ _

/-- **THREE-GENERATOR ASSOCIATIVE CLOSURE ACHIEVED.**  The span of the eight
derived elements contains the unit and the three inherited spatial generators
and is closed under the ambient product. -/
theorem G3_is_closed_subspace :
    S.oneE ∈ G3 S ∧ S.genA ∈ G3 S ∧ S.genB ∈ G3 S ∧ genC S ∈ G3 S ∧
      ∀ x ∈ G3 S, ∀ y ∈ G3 S, S.mul x y ∈ G3 S :=
  ⟨oneE_mem_G3 S, genA_mem_G3 S, genB_mem_G3 S, genC_mem_G3 S,
    fun _ hx _ hy => G3_mul_closed S hx hy⟩

/-! ## Exact dimension -/

/-- **EXACT DIMENSION (DERIVED).**  The minimal three-generator closure has real
dimension eight.  The number was never an input: the ambient carrier `E` keeps
an unspecified dimension throughout. -/
theorem finrank_G3 : Module.finrank ℝ (G3 S) = 8 := by
  rw [G3, finrank_span_eq_card (genFamily8_linearIndependent S)]
  simp

/-! ## The complete multiplication table -/

/-- **DERIVED MULTIPLICATION TABLE (row of the unit).** -/
theorem table_one :
    S.mul S.oneE S.oneE = S.oneE ∧ S.mul S.oneE S.genA = S.genA ∧
    S.mul S.oneE S.genB = S.genB ∧ S.mul S.oneE (genC S) = genC S ∧
    S.mul S.oneE S.genP = S.genP ∧ S.mul S.oneE (genQ S) = genQ S ∧
    S.mul S.oneE (genR S) = genR S ∧ S.mul S.oneE (genS S) = genS S :=
  ⟨S.one_mul' _, S.one_mul' _, S.one_mul' _, S.one_mul' _, S.one_mul' _,
    S.one_mul' _, S.one_mul' _, S.one_mul' _⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `A`).** -/
theorem table_genA :
    S.mul S.genA S.oneE = S.genA ∧ S.mul S.genA S.genA = S.oneE ∧
    S.mul S.genA S.genB = S.genP ∧ S.mul S.genA (genC S) = genQ S ∧
    S.mul S.genA S.genP = S.genB ∧ S.mul S.genA (genQ S) = genC S ∧
    S.mul S.genA (genR S) = genS S ∧ S.mul S.genA (genS S) = genR S :=
  ⟨S.mul_one' _, S.genA_sq, S.mul_genA_genB, mul_genA_genC S, S.mul_genA_genP,
    mul_genA_genQ S, mul_genA_genR S, mul_genA_genS S⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `B`).** -/
theorem table_genB :
    S.mul S.genB S.oneE = S.genB ∧ S.mul S.genB S.genA = - S.genP ∧
    S.mul S.genB S.genB = S.oneE ∧ S.mul S.genB (genC S) = genR S ∧
    S.mul S.genB S.genP = - S.genA ∧ S.mul S.genB (genQ S) = - genS S ∧
    S.mul S.genB (genR S) = genC S ∧ S.mul S.genB (genS S) = - genQ S :=
  ⟨S.mul_one' _, S.mul_genB_genA, S.genB_sq, mul_genB_genC S, S.mul_genB_genP,
    mul_genB_genQ S, mul_genB_genR S, mul_genB_genS S⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `C`).** -/
theorem table_genC :
    S.mul (genC S) S.oneE = genC S ∧ S.mul (genC S) S.genA = - genQ S ∧
    S.mul (genC S) S.genB = - genR S ∧ S.mul (genC S) (genC S) = S.oneE ∧
    S.mul (genC S) S.genP = genS S ∧ S.mul (genC S) (genQ S) = - S.genA ∧
    S.mul (genC S) (genR S) = - S.genB ∧ S.mul (genC S) (genS S) = S.genP :=
  ⟨S.mul_one' _, mul_genC_genA S, mul_genC_genB S, genC_sq S, mul_genC_genP S,
    mul_genC_genQ S, mul_genC_genR S, mul_genC_genS S⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `P`).** -/
theorem table_genP :
    S.mul S.genP S.oneE = S.genP ∧ S.mul S.genP S.genA = - S.genB ∧
    S.mul S.genP S.genB = S.genA ∧ S.mul S.genP (genC S) = genS S ∧
    S.mul S.genP S.genP = - S.oneE ∧ S.mul S.genP (genQ S) = - genR S ∧
    S.mul S.genP (genR S) = genQ S ∧ S.mul S.genP (genS S) = - genC S :=
  ⟨S.mul_one' _, S.mul_genP_genA, S.mul_genP_genB, mul_genP_genC S, S.genP_sq,
    mul_genP_genQ S, mul_genP_genR S, mul_genP_genS S⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `Q`).** -/
theorem table_genQ :
    S.mul (genQ S) S.oneE = genQ S ∧ S.mul (genQ S) S.genA = - genC S ∧
    S.mul (genQ S) S.genB = - genS S ∧ S.mul (genQ S) (genC S) = S.genA ∧
    S.mul (genQ S) S.genP = genR S ∧ S.mul (genQ S) (genQ S) = - S.oneE ∧
    S.mul (genQ S) (genR S) = - S.genP ∧ S.mul (genQ S) (genS S) = S.genB :=
  ⟨S.mul_one' _, mul_genQ_genA S, genQ_mul_genB S, mul_genQ_genC S, mul_genQ_genP S,
    genQ_sq S, mul_genQ_genR S, mul_genQ_genS S⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `R`).** -/
theorem table_genR :
    S.mul (genR S) S.oneE = genR S ∧ S.mul (genR S) S.genA = genS S ∧
    S.mul (genR S) S.genB = - genC S ∧ S.mul (genR S) (genC S) = S.genB ∧
    S.mul (genR S) S.genP = - genQ S ∧ S.mul (genR S) (genQ S) = S.genP ∧
    S.mul (genR S) (genR S) = - S.oneE ∧ S.mul (genR S) (genS S) = - S.genA :=
  ⟨S.mul_one' _, mul_genR_genA S, mul_genR_genB S, mul_genR_genC S, mul_genR_genP S,
    mul_genR_genQ S, genR_sq S, mul_genR_genS S⟩

/-- **DERIVED MULTIPLICATION TABLE (row of `S₃`).** -/
theorem table_genS :
    S.mul (genS S) S.oneE = genS S ∧ S.mul (genS S) S.genA = genR S ∧
    S.mul (genS S) S.genB = - genQ S ∧ S.mul (genS S) (genC S) = S.genP ∧
    S.mul (genS S) S.genP = - genC S ∧ S.mul (genS S) (genQ S) = S.genB ∧
    S.mul (genS S) (genR S) = - S.genA ∧ S.mul (genS S) (genS S) = - S.oneE :=
  ⟨S.mul_one' _, mul_genS_genA S, mul_genS_genB S, mul_genS_genC S, mul_genS_genP S,
    mul_genS_genQ S, mul_genS_genR S, genS_sq S⟩

end NullSectorTask08
