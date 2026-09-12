import RequestProject.Experiment2.NullSectorTask08.NewMixedProducts

/-!
# Task 08, Layer 4: the complete ledger of forced relations

Every statement of this module is a **theorem output**.  The only inputs are

* the inherited squares `A ⋆ A = B ⋆ B = C ⋆ C = 1`,
* the derived pairwise anticommutation relations,
* associativity and bilinearity of the ambient product,
* the definitions `P := A ⋆ B`, `Q := A ⋆ C`, `R := B ⋆ C`, `S₃ := P ⋆ C`.

No multiplication table is assumed; the table collected in
`GeneratedClosure.lean` is assembled *from* these theorems.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-! ## Products of `A`, `B`, `C` with `Q` -/

/-- `A ⋆ Q = C`. -/
theorem mul_genA_genQ : S.mul S.genA (genQ S) = genC S := by
  rw [genQ, ← S.assoc, S.genA_sq, S.one_mul']

/-- `Q ⋆ A = -C`. -/
theorem mul_genQ_genA : S.mul (genQ S) S.genA = - genC S := by
  rw [genQ, S.assoc, mul_genC_genA, mul_neg_right, mul_genA_genQ]

/-- `B ⋆ Q = -S₃`. -/
theorem mul_genB_genQ : S.mul S.genB (genQ S) = - genS S := by
  rw [genQ, ← S.assoc, S.mul_genB_genA, mul_neg_left, mul_genP_genC]

/-- `Q ⋆ C = A`. -/
theorem mul_genQ_genC : S.mul (genQ S) (genC S) = S.genA := by
  rw [genQ, S.assoc, genC_sq, S.mul_one']

/-- `C ⋆ Q = -A`. -/
theorem mul_genC_genQ : S.mul (genC S) (genQ S) = - S.genA := by
  rw [genQ, ← S.assoc, mul_genC_genA, mul_neg_left, mul_genQ_genC]

/-! ## Products of `A`, `B`, `C` with `R` -/

/-- `A ⋆ R = S₃`. -/
theorem mul_genA_genR : S.mul S.genA (genR S) = genS S := (genS_eq_genA_mul_genR S).symm

/-- `B ⋆ R = C`. -/
theorem mul_genB_genR : S.mul S.genB (genR S) = genC S := by
  rw [genR, ← S.assoc, S.genB_sq, S.one_mul']

/-- `R ⋆ B = -C`. -/
theorem mul_genR_genB : S.mul (genR S) S.genB = - genC S := by
  rw [genR, S.assoc, mul_genC_genB, mul_neg_right, mul_genB_genR]

/-- `R ⋆ C = B`. -/
theorem mul_genR_genC : S.mul (genR S) (genC S) = S.genB := by
  rw [genR, S.assoc, genC_sq, S.mul_one']

/-- `C ⋆ R = -B`. -/
theorem mul_genC_genR : S.mul (genC S) (genR S) = - S.genB := by
  rw [genR, ← S.assoc, mul_genC_genB, mul_neg_left, mul_genR_genC]

/-- `R ⋆ A = S₃`. -/
theorem mul_genR_genA : S.mul (genR S) S.genA = genS S := by
  rw [genR, S.assoc, mul_genC_genA, mul_neg_right, mul_genB_genQ, neg_neg]

/-! ## Products of `C` with the Task-07 channel `P` -/

/-- `C ⋆ P = S₃`. -/
theorem mul_genC_genP : S.mul (genC S) S.genP = genS S := by
  rw [← S.mul_genA_genB, ← S.assoc, mul_genC_genA, mul_neg_left, genQ_mul_genB, neg_neg]

/-! ## Products of the generators with `S₃` -/

/-- `A ⋆ S₃ = R`. -/
theorem mul_genA_genS : S.mul S.genA (genS S) = genR S := by
  rw [genS, ← S.assoc, S.mul_genA_genP, mul_genB_genC]

/-- `P ⋆ Q = -R`. -/
theorem mul_genP_genQ : S.mul S.genP (genQ S) = - genR S := by
  rw [genQ, ← S.assoc, S.mul_genP_genA, mul_neg_left, mul_genB_genC]

/-- `S₃ ⋆ A = R`. -/
theorem mul_genS_genA : S.mul (genS S) S.genA = genR S := by
  rw [genS, S.assoc, mul_genC_genA, mul_neg_right, mul_genP_genQ, neg_neg]

/-- `B ⋆ S₃ = -Q`. -/
theorem mul_genB_genS : S.mul S.genB (genS S) = - genQ S := by
  rw [genS, ← S.assoc, S.mul_genB_genP, mul_neg_left, mul_genA_genC]

/-- `P ⋆ R = Q`. -/
theorem mul_genP_genR : S.mul S.genP (genR S) = genQ S := by
  rw [genR, ← S.assoc, S.mul_genP_genB, mul_genA_genC]

/-- `S₃ ⋆ B = -Q`. -/
theorem mul_genS_genB : S.mul (genS S) S.genB = - genQ S := by
  rw [genS, S.assoc, mul_genC_genB, mul_neg_right, mul_genP_genR]

/-- `S₃ ⋆ C = P`. -/
theorem mul_genS_genC : S.mul (genS S) (genC S) = S.genP := by
  rw [genS, S.assoc, genC_sq, S.mul_one']

/-- `C ⋆ S₃ = P`. -/
theorem mul_genC_genS : S.mul (genC S) (genS S) = S.genP := by
  rw [genS, ← S.assoc, mul_genC_genP, mul_genS_genC]

/-- `P ⋆ S₃ = -C`. -/
theorem mul_genP_genS : S.mul S.genP (genS S) = - genC S := by
  rw [genS, ← S.assoc, S.genP_sq, mul_neg_left, S.one_mul']

/-- `S₃ ⋆ P = -C`. -/
theorem mul_genS_genP : S.mul (genS S) S.genP = - genC S := by
  rw [genS, S.assoc, mul_genC_genP, mul_genP_genS]

/-- `Q ⋆ P = R`. -/
theorem mul_genQ_genP : S.mul (genQ S) S.genP = genR S := by
  rw [genQ, S.assoc, mul_genC_genP, mul_genA_genS]

/-- `R ⋆ P = -Q`. -/
theorem mul_genR_genP : S.mul (genR S) S.genP = - genQ S := by
  rw [genR, S.assoc, mul_genC_genP, mul_genB_genS]

/-! ## Squares of the new channels -/

/-- **DERIVED.**  `Q ⋆ Q = -1`. -/
theorem genQ_sq : S.mul (genQ S) (genQ S) = - S.oneE := by
  have h : S.mul (genQ S) (genQ S) = S.mul S.genA (S.mul (genC S) (genQ S)) := by
    rw [genQ_def]; exact S.assoc _ _ _
  rw [h, mul_genC_genQ, mul_neg_right, S.genA_sq]

/-- **DERIVED.**  `R ⋆ R = -1`. -/
theorem genR_sq : S.mul (genR S) (genR S) = - S.oneE := by
  have h : S.mul (genR S) (genR S) = S.mul S.genB (S.mul (genC S) (genR S)) := by
    rw [genR_def]; exact S.assoc _ _ _
  rw [h, mul_genC_genR, mul_neg_right, S.genB_sq]

/-- **DERIVED.**  `S₃ ⋆ S₃ = -1`. -/
theorem genS_sq : S.mul (genS S) (genS S) = - S.oneE := by
  have h : S.mul (genS S) (genS S) = S.mul S.genP (S.mul (genC S) (genS S)) := by
    rw [genS_def]; exact S.assoc _ _ _
  rw [h, mul_genC_genS, S.genP_sq]

/-! ## Products among `Q`, `R` and `S₃` -/

/-- `Q ⋆ R = -P`. -/
theorem mul_genQ_genR : S.mul (genQ S) (genR S) = - S.genP := by
  conv_lhs => rw [genQ]
  rw [S.assoc, mul_genC_genR, mul_neg_right, S.mul_genA_genB]

/-- `R ⋆ Q = P`. -/
theorem mul_genR_genQ : S.mul (genR S) (genQ S) = S.genP := by
  conv_lhs => rw [genR]
  rw [S.assoc, mul_genC_genQ, mul_neg_right, S.mul_genB_genA, neg_neg]

/-- `Q ⋆ S₃ = B`. -/
theorem mul_genQ_genS : S.mul (genQ S) (genS S) = S.genB := by
  conv_lhs => rw [genQ]
  rw [S.assoc, mul_genC_genS, S.mul_genA_genP]

/-- `S₃ ⋆ Q = B`. -/
theorem mul_genS_genQ : S.mul (genS S) (genQ S) = S.genB := by
  conv_lhs => rw [genS]
  rw [S.assoc, mul_genC_genQ, mul_neg_right, S.mul_genP_genA, neg_neg]

/-- `R ⋆ S₃ = -A`. -/
theorem mul_genR_genS : S.mul (genR S) (genS S) = - S.genA := by
  conv_lhs => rw [genR]
  rw [S.assoc, mul_genC_genS, S.mul_genB_genP]

/-- `S₃ ⋆ R = -A`. -/
theorem mul_genS_genR : S.mul (genS S) (genR S) = - S.genA := by
  conv_lhs => rw [genS]
  rw [S.assoc, mul_genC_genR, mul_neg_right, S.mul_genP_genB]

/-! ## Summary ledgers -/

/-- **FORCED RELATIONS: interaction of the old generators with `Q` and `R`.** -/
theorem forced_relations_old_generators :
    S.mul S.genA (genQ S) = genC S ∧ S.mul (genQ S) S.genA = - genC S ∧
    S.mul S.genB (genQ S) = - genS S ∧ S.mul (genQ S) S.genB = - genS S ∧
    S.mul (genC S) (genQ S) = - S.genA ∧ S.mul (genQ S) (genC S) = S.genA ∧
    S.mul S.genA (genR S) = genS S ∧ S.mul (genR S) S.genA = genS S ∧
    S.mul S.genB (genR S) = genC S ∧ S.mul (genR S) S.genB = - genC S ∧
    S.mul (genC S) (genR S) = - S.genB ∧ S.mul (genR S) (genC S) = S.genB :=
  ⟨mul_genA_genQ S, mul_genQ_genA S, mul_genB_genQ S, genQ_mul_genB S,
    mul_genC_genQ S, mul_genQ_genC S, mul_genA_genR S, mul_genR_genA S,
    mul_genB_genR S, mul_genR_genB S, mul_genC_genR S, mul_genR_genC S⟩

/-- **FORCED RELATIONS: interaction of the old generators with `S₃`.** -/
theorem forced_relations_genS :
    S.mul S.genA (genS S) = genR S ∧ S.mul (genS S) S.genA = genR S ∧
    S.mul S.genB (genS S) = - genQ S ∧ S.mul (genS S) S.genB = - genQ S ∧
    S.mul (genC S) (genS S) = S.genP ∧ S.mul (genS S) (genC S) = S.genP :=
  ⟨mul_genA_genS S, mul_genS_genA S, mul_genB_genS S, mul_genS_genB S,
    mul_genC_genS S, mul_genS_genC S⟩

/-- **FORCED RELATIONS: interaction with the Task-07 channel `P`.** -/
theorem forced_relations_genP :
    S.mul S.genP (genQ S) = - genR S ∧ S.mul (genQ S) S.genP = genR S ∧
    S.mul S.genP (genR S) = genQ S ∧ S.mul (genR S) S.genP = - genQ S ∧
    S.mul S.genP (genS S) = - genC S ∧ S.mul (genS S) S.genP = - genC S :=
  ⟨mul_genP_genQ S, mul_genQ_genP S, mul_genP_genR S, mul_genR_genP S,
    mul_genP_genS S, mul_genS_genP S⟩

/-- **FORCED RELATIONS: the new channels among themselves.** -/
theorem forced_relations_new_channels :
    S.mul (genQ S) (genQ S) = - S.oneE ∧ S.mul (genR S) (genR S) = - S.oneE ∧
    S.mul (genS S) (genS S) = - S.oneE ∧
    S.mul (genQ S) (genR S) = - S.genP ∧ S.mul (genR S) (genQ S) = S.genP ∧
    S.mul (genQ S) (genS S) = S.genB ∧ S.mul (genS S) (genQ S) = S.genB ∧
    S.mul (genR S) (genS S) = - S.genA ∧ S.mul (genS S) (genR S) = - S.genA :=
  ⟨genQ_sq S, genR_sq S, genS_sq S, mul_genQ_genR S, mul_genR_genQ S,
    mul_genQ_genS S, mul_genS_genQ S, mul_genR_genS S, mul_genS_genR S⟩

end NullSectorTask08
