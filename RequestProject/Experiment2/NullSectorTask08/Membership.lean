import RequestProject.Experiment2.NullSectorTask08.ForcedRelations

/-!
# Task 08, Layer 5: membership classification

Two separate questions are settled here, both by *structural* arguments (no
dimension counting):

1. **Old-carrier membership.**  Which of `P, Q, R, S₃` are images of vectors of
   the original carrier?  Answer: none of them; the obstruction is the same
   inherited real-positivity obstruction used in Task 07 for `P`, applied to
   each channel through its independently derived square.
2. **Task-07 closure membership.**  Which of `C, Q, R, S₃` lie in
   `G₂ = span_ℝ {1, A, B, P}`?  Answer: none of them.  The proof uses the two
   conjugation operations `x ↦ A ⋆ x ⋆ A` and `x ↦ B ⋆ x ⋆ B`, whose effect on
   the Task-07 normal form is computed from the derived relations, together
   with the inherited Task-07 independence theorem and the derived squares.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-! ## Old-carrier membership -/

/-- **OBSTRUCTION (generic form).**  No element whose square is `-1` is the
image of a vector of the original carrier: the inherited square law would force
`oldSq X = -e₀`, whose time component is a sum of real squares. -/
theorem not_image_of_sq_eq_neg_one {x : E} (hx : S.mul x x = - S.oneE) :
    ¬ ∃ X : Vec4, S.iota X = x := by
  rintro ⟨X, hX⟩
  have hsq : S.iota (oldSq X) = S.iota (- e₀) := by
    rw [← S.oldsq X, hX, hx, map_neg, S.iota_e₀]
  exact oldSq_ne_neg_e₀ X (S.iota_inj hsq)

/-- **OUTSIDE OLD CARRIER.**  `Q ∉ ι(Vec4)`. -/
theorem genQ_not_mem_range : genQ S ∉ LinearMap.range S.iota := by
  intro hmem
  exact not_image_of_sq_eq_neg_one S (genQ_sq S)
    (by simpa [LinearMap.mem_range] using hmem)

/-- **OUTSIDE OLD CARRIER.**  `R ∉ ι(Vec4)`. -/
theorem genR_not_mem_range : genR S ∉ LinearMap.range S.iota := by
  intro hmem
  exact not_image_of_sq_eq_neg_one S (genR_sq S)
    (by simpa [LinearMap.mem_range] using hmem)

/-- **OUTSIDE OLD CARRIER.**  `S₃ ∉ ι(Vec4)`. -/
theorem genS_not_mem_range : genS S ∉ LinearMap.range S.iota := by
  intro hmem
  exact not_image_of_sq_eq_neg_one S (genS_sq S)
    (by simpa [LinearMap.mem_range] using hmem)

/-- **INSIDE OLD CARRIER.**  The third generator is, by construction, the image
of an old vector. -/
theorem genC_mem_range : genC S ∈ LinearMap.range S.iota := ⟨dirC, rfl⟩

/-- **OLD-CARRIER CLASSIFICATION.**  `C` is inside the embedded old carrier;
`P`, `Q`, `R`, `S₃` are all outside it. -/
theorem old_carrier_classification :
    genC S ∈ LinearMap.range S.iota ∧
    S.genP ∉ LinearMap.range S.iota ∧
    genQ S ∉ LinearMap.range S.iota ∧
    genR S ∉ LinearMap.range S.iota ∧
    genS S ∉ LinearMap.range S.iota :=
  ⟨genC_mem_range S, S.genP_not_mem_range, genQ_not_mem_range S,
    genR_not_mem_range S, genS_not_mem_range S⟩

/-! ## Conjugation by the first two generators -/

/-- Conjugation of `x` by an element `g`. -/
def conjBy (g x : E) : E := S.mul (S.mul g x) g

/-- **DERIVED.**  Conjugation by `A` on the Task-07 normal form. -/
theorem conjBy_genA_gcomb (α β γ δ : ℝ) :
    conjBy S S.genA (S.gcomb α β γ δ) = S.gcomb α β (-γ) (-δ) := by
  simp only [conjBy, AmbientExt.gcomb, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, S.mul_one', S.one_mul',
    S.genA_sq, S.mul_genA_genB, S.mul_genA_genP, S.mul_genB_genA, S.mul_genP_genA]
  module

/-- **DERIVED.**  Conjugation by `B` on the Task-07 normal form. -/
theorem conjBy_genB_gcomb (α β γ δ : ℝ) :
    conjBy S S.genB (S.gcomb α β γ δ) = S.gcomb α (-β) γ (-δ) := by
  simp only [conjBy, AmbientExt.gcomb, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, mul_neg_left, S.mul_one', S.one_mul',
    S.genB_sq, S.mul_genA_genB, S.mul_genB_genA,
    S.mul_genP_genB, S.mul_genB_genP]
  module

/-! ## The two conjugation selection rules -/

theorem gcomb_of_conjA_neg {α β γ δ : ℝ}
    (h : conjBy S S.genA (S.gcomb α β γ δ) = - S.gcomb α β γ δ) :
    α = 0 ∧ β = 0 := by
  rw [conjBy_genA_gcomb] at h
  have h' : S.gcomb α β (-γ) (-δ) = S.gcomb (-α) (-β) (-γ) (-δ) := by
    rw [h]; simp only [AmbientExt.gcomb]; module
  obtain ⟨h1, h2, _, _⟩ := S.gcomb_injective h'
  constructor <;> linarith

theorem gcomb_of_conjA_self {α β γ δ : ℝ}
    (h : conjBy S S.genA (S.gcomb α β γ δ) = S.gcomb α β γ δ) :
    γ = 0 ∧ δ = 0 := by
  rw [conjBy_genA_gcomb] at h
  obtain ⟨_, _, h3, h4⟩ := S.gcomb_injective h
  constructor <;> linarith

theorem gcomb_of_conjB_neg {α β γ δ : ℝ}
    (h : conjBy S S.genB (S.gcomb α β γ δ) = - S.gcomb α β γ δ) :
    α = 0 ∧ γ = 0 := by
  rw [conjBy_genB_gcomb] at h
  have h' : S.gcomb α (-β) γ (-δ) = S.gcomb (-α) (-β) (-γ) (-δ) := by
    rw [h]; simp only [AmbientExt.gcomb]; module
  obtain ⟨h1, _, h3, _⟩ := S.gcomb_injective h'
  constructor <;> linarith

theorem gcomb_of_conjB_self {α β γ δ : ℝ}
    (h : conjBy S S.genB (S.gcomb α β γ δ) = S.gcomb α β γ δ) :
    β = 0 ∧ δ = 0 := by
  rw [conjBy_genB_gcomb] at h
  obtain ⟨_, h2, _, h4⟩ := S.gcomb_injective h
  constructor <;> linarith

/-! ## Conjugation values of the four channels -/

theorem conjBy_genA_genC : conjBy S S.genA (genC S) = - genC S := by
  rw [conjBy, mul_genA_genC, mul_genQ_genA]

theorem conjBy_genB_genC : conjBy S S.genB (genC S) = - genC S := by
  rw [conjBy, mul_genB_genC, mul_genR_genB]

theorem conjBy_genA_genQ : conjBy S S.genA (genQ S) = - genQ S := by
  rw [conjBy, mul_genA_genQ, mul_genC_genA]

theorem conjBy_genB_genQ : conjBy S S.genB (genQ S) = genQ S := by
  rw [conjBy, mul_genB_genQ, mul_neg_left, mul_genS_genB, neg_neg]

theorem conjBy_genA_genR : conjBy S S.genA (genR S) = genR S := by
  rw [conjBy, mul_genA_genR, mul_genS_genA]

theorem conjBy_genB_genR : conjBy S S.genB (genR S) = - genR S := by
  rw [conjBy, mul_genB_genR, mul_genC_genB]

theorem conjBy_genA_genS : conjBy S S.genA (genS S) = genS S := by
  rw [conjBy, mul_genA_genS, mul_genR_genA]

theorem conjBy_genB_genS : conjBy S S.genB (genS S) = genS S := by
  rw [conjBy, mul_genB_genS, mul_neg_left, genQ_mul_genB, neg_neg]

/-! ## Non-membership in the Task-07 closure -/

/-- A real multiple of the unit cannot have square `-1` or `+1` with the wrong
sign: the elementary scalar obstruction used four times below. -/
theorem scalar_obstruction {c : ℝ} {y : E} (hy : S.mul y y = S.oneE)
    (hx : S.mul (c • y) (c • y) = - S.oneE) : False := by
  have h1 : S.mul (c • y) (c • y) = (c * c) • S.oneE := by
    simp only [map_smul, LinearMap.smul_apply, hy, smul_smul]
  rw [h1] at hx
  have h0 : (c * c + 1) • S.oneE = 0 := by
    rw [add_smul, one_smul, hx]; abel
  rcases smul_eq_zero.1 h0 with h | h
  · nlinarith
  · exact S.oneE_ne_zero h

theorem scalar_obstruction' {c : ℝ} {y : E} (hy : S.mul y y = - S.oneE)
    (hx : S.mul (c • y) (c • y) = S.oneE) : False := by
  have h1 : S.mul (c • y) (c • y) = (c * c) • (- S.oneE) := by
    simp only [map_smul, LinearMap.smul_apply, hy, smul_smul]
  rw [h1] at hx
  have h0 : (c * c + 1) • S.oneE = 0 := by
    linear_combination (norm := module) - hx
  rcases smul_eq_zero.1 h0 with h | h
  · nlinarith
  · exact S.oneE_ne_zero h

/-- **OUTSIDE TWO-GENERATOR CLOSURE.**  `C ∉ G₂`. -/
theorem genC_not_mem_Gsub : genC S ∉ S.Gsub := by
  intro hmem
  obtain ⟨α, β, γ, δ, hC⟩ := (S.mem_Gsub_iff _).1 hmem
  have hA : conjBy S S.genA (S.gcomb α β γ δ) = - S.gcomb α β γ δ := by
    rw [← hC]; exact conjBy_genA_genC S
  have hB : conjBy S S.genB (S.gcomb α β γ δ) = - S.gcomb α β γ δ := by
    rw [← hC]; exact conjBy_genB_genC S
  obtain ⟨hα, hβ⟩ := gcomb_of_conjA_neg S hA
  obtain ⟨_, hγ⟩ := gcomb_of_conjB_neg S hB
  subst hα; subst hβ; subst hγ
  have hCP : genC S = δ • S.genP := by rw [hC]; simp only [AmbientExt.gcomb]; module
  refine scalar_obstruction' (c := δ) S S.genP_sq ?_
  rw [← hCP]; exact genC_sq S

/-- **OUTSIDE TWO-GENERATOR CLOSURE.**  `Q ∉ G₂`. -/
theorem genQ_not_mem_Gsub : genQ S ∉ S.Gsub := by
  intro hmem
  obtain ⟨α, β, γ, δ, hQ⟩ := (S.mem_Gsub_iff _).1 hmem
  have hA : conjBy S S.genA (S.gcomb α β γ δ) = - S.gcomb α β γ δ := by
    rw [← hQ]; exact conjBy_genA_genQ S
  have hB : conjBy S S.genB (S.gcomb α β γ δ) = S.gcomb α β γ δ := by
    rw [← hQ]; exact conjBy_genB_genQ S
  obtain ⟨hα, hβ⟩ := gcomb_of_conjA_neg S hA
  obtain ⟨_, hδ⟩ := gcomb_of_conjB_self S hB
  subst hα; subst hβ; subst hδ
  have hQB : genQ S = γ • S.genB := by rw [hQ]; simp only [AmbientExt.gcomb]; module
  refine scalar_obstruction (c := γ) S S.genB_sq ?_
  rw [← hQB]; exact genQ_sq S

/-- **OUTSIDE TWO-GENERATOR CLOSURE.**  `R ∉ G₂`. -/
theorem genR_not_mem_Gsub : genR S ∉ S.Gsub := by
  intro hmem
  obtain ⟨α, β, γ, δ, hR⟩ := (S.mem_Gsub_iff _).1 hmem
  have hA : conjBy S S.genA (S.gcomb α β γ δ) = S.gcomb α β γ δ := by
    rw [← hR]; exact conjBy_genA_genR S
  have hB : conjBy S S.genB (S.gcomb α β γ δ) = - S.gcomb α β γ δ := by
    rw [← hR]; exact conjBy_genB_genR S
  obtain ⟨hγ, hδ⟩ := gcomb_of_conjA_self S hA
  obtain ⟨hα, _⟩ := gcomb_of_conjB_neg S hB
  subst hγ; subst hδ; subst hα
  have hRA : genR S = β • S.genA := by rw [hR]; simp only [AmbientExt.gcomb]; module
  refine scalar_obstruction (c := β) S S.genA_sq ?_
  rw [← hRA]; exact genR_sq S

/-- **OUTSIDE TWO-GENERATOR CLOSURE.**  `S₃ ∉ G₂`. -/
theorem genS_not_mem_Gsub : genS S ∉ S.Gsub := by
  intro hmem
  obtain ⟨α, β, γ, δ, hS⟩ := (S.mem_Gsub_iff _).1 hmem
  have hA : conjBy S S.genA (S.gcomb α β γ δ) = S.gcomb α β γ δ := by
    rw [← hS]; exact conjBy_genA_genS S
  have hB : conjBy S S.genB (S.gcomb α β γ δ) = S.gcomb α β γ δ := by
    rw [← hS]; exact conjBy_genB_genS S
  obtain ⟨hγ, hδ⟩ := gcomb_of_conjA_self S hA
  obtain ⟨hβ, _⟩ := gcomb_of_conjB_self S hB
  subst hγ; subst hδ; subst hβ
  have hS1 : genS S = α • S.oneE := by rw [hS]; simp only [AmbientExt.gcomb]; module
  refine scalar_obstruction (c := α) S (S.one_mul' S.oneE) ?_
  rw [← hS1]; exact genS_sq S

/-- **MEMBERSHIP CLASSIFICATION (summary).**  None of the third generator and
the three new channels belongs to the Task-07 two-generator closure. -/
theorem Gsub_membership_classification :
    genC S ∉ S.Gsub ∧ genQ S ∉ S.Gsub ∧ genR S ∉ S.Gsub ∧ genS S ∉ S.Gsub :=
  ⟨genC_not_mem_Gsub S, genQ_not_mem_Gsub S, genR_not_mem_Gsub S,
    genS_not_mem_Gsub S⟩

end NullSectorTask08
