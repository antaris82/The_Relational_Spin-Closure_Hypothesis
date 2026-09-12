import RequestProject.Experiment2.NullSectorTask02.CandidateProduct

/-!
# Task 02, Layer 3: complete classification of the products admissible at `u₀`

The reference vector `u₀ = (1,0)` is an **explicit additional datum**: it is a
vector of the coordinate carrier, not something singled out by `Q2` alone
(see `GeneralUnit.lean` and `Canonicality.lean`).

Everything in this file starts from a *generic* `μ : BiProd` satisfying
`AdmissibleAt u₀ μ`.  The coordinate formula of the product, the square relation
`μ s₀ s₀ = u₀`, commutativity, associativity, and the idempotent structure are
all **derived**.
-/

namespace NullSectorTask02

open NullSectorTask01

section FixedUnit

variable {μ : BiProd} (h : AdmissibleAt u₀ μ)

include h

theorem mu_u₀_u₀ : μ u₀ u₀ = u₀ := h.1.1 u₀
theorem mu_u₀_s₀ : μ u₀ s₀ = s₀ := h.1.1 s₀
theorem mu_s₀_u₀ : μ s₀ u₀ = s₀ := h.1.2 s₀

/-- Generic shape of an admissible product at `u₀`: everything is determined by the
single unknown vector `μ s₀ s₀`. -/
theorem mu_shape (X Y : Long) :
    μ X Y = (X.1 * Y.1 + X.2 * Y.2 * (μ s₀ s₀).1,
             X.1 * Y.2 + X.2 * Y.1 + X.2 * Y.2 * (μ s₀ s₀).2) := by
  rw [bilin_expand μ X Y, mu_u₀_u₀ h, mu_u₀_s₀ h, mu_s₀_u₀ h]
  apply Prod.ext <;> simp [u₀, s₀]

/-- **Derived square relation.**  `Q2`-multiplicativity plus the two-sided unit law
force the square of the second coordinate vector. -/
theorem mu_s₀_s₀ : μ s₀ s₀ = u₀ := by
  have e1 : Q2 (μ s₀ s₀) = Q2 s₀ * Q2 s₀ := h.2 s₀ s₀
  have e2 : Q2 (μ (1, 1) s₀) = Q2 ((1, 1) : Long) * Q2 s₀ := h.2 (1, 1) s₀
  have e3 : Q2 (μ (1, 1) (1, 1)) = Q2 ((1, 1) : Long) * Q2 ((1, 1) : Long) := h.2 (1, 1) (1, 1)
  rw [mu_shape h] at e2 e3
  rcases hw : μ s₀ s₀ with ⟨w1, w2⟩
  rw [hw] at e1 e2 e3
  simp [Q2, s₀] at e1 e2 e3
  have hw2 : w2 = 0 := by nlinarith [e1, e2]
  have hw1 : w1 = 1 := by nlinarith [e1, e3, hw2]
  simp [u₀, hw1, hw2]

/-- **Complete fixed-unit classification.**  Every bilinear product with two-sided
unit `u₀` satisfying `Q2 (μ X Y) = Q2 X * Q2 Y` has exactly this coordinate formula. -/
theorem fixedUnit_formula (X Y : Long) :
    μ X Y = (X.1 * Y.1 + X.2 * Y.2, X.1 * Y.2 + X.2 * Y.1) := by
  rw [mu_shape h, mu_s₀_s₀ h]
  apply Prod.ext <;> simp [u₀]

/-- Commutativity is a **consequence**, not an assumption. -/
theorem fixedUnit_commutative : Commutative μ := by
  intro X Y
  rw [fixedUnit_formula h, fixedUnit_formula h]
  apply Prod.ext <;> simp <;> ring

/-- Associativity is a **consequence**, not an assumption. -/
theorem fixedUnit_associative : Associative μ := by
  intro X Y Z
  rw [fixedUnit_formula h, fixedUnit_formula h, fixedUnit_formula h, fixedUnit_formula h]
  apply Prod.ext <;> simp <;> ring

end FixedUnit

/-- **Uniqueness at the chosen unit.**  Any two products admissible at `u₀` are equal. -/
theorem fixedUnit_unique {μ ν : BiProd} (hμ : AdmissibleAt u₀ μ) (hν : AdmissibleAt u₀ ν) :
    μ = ν := by
  apply LinearMap.ext; intro X
  apply LinearMap.ext; intro Y
  rw [fixedUnit_formula hμ, fixedUnit_formula hν]

/-!
### Existence at `u₀`

The classification above says *at most one* product is admissible at `u₀`; the
formula it produces is now checked to be a genuine bilinear, unital,
`Q2`-multiplicative product, so exactly one exists.
-/

/-- The product produced by the classification, written as a bilinear map. -/
noncomputable def recU : BiProd :=
  LinearMap.mk₂ ℝ (fun X Y => ((X.1 * Y.1 + X.2 * Y.2 : ℝ), (X.1 * Y.2 + X.2 * Y.1 : ℝ)))
    (by intro X₁ X₂ Y; apply Prod.ext <;> simp <;> ring)
    (by intro c X Y; apply Prod.ext <;> simp <;> ring)
    (by intro X Y₁ Y₂; apply Prod.ext <;> simp <;> ring)
    (by intro c X Y; apply Prod.ext <;> simp <;> ring)

@[simp] theorem recU_apply (X Y : Long) :
    recU X Y = (X.1 * Y.1 + X.2 * Y.2, X.1 * Y.2 + X.2 * Y.1) := rfl

theorem recU_admissible : AdmissibleAt u₀ recU := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro X; apply Prod.ext <;> simp [u₀]
  · intro X; apply Prod.ext <;> simp [u₀]
  · intro X Y; simp [Q2]; ring

/-- **Existence and uniqueness at `u₀`.** -/
theorem fixedUnit_existsUnique : ∃! μ : BiProd, AdmissibleAt u₀ μ :=
  ⟨recU, recU_admissible, fun _ hν => fixedUnit_unique hν recU_admissible⟩

/-!
### Complementary candidate idempotents

Defined here from `u₀` and `s₀` only, independently of any Task-01 declaration.
-/

/-- `p₊ := (1/2) • (u₀ + s₀)`. -/
noncomputable def pplus : Long := (1 / 2 : ℝ) • (u₀ + s₀)

/-- `p₋ := (1/2) • (u₀ - s₀)`. -/
noncomputable def pminus : Long := (1 / 2 : ℝ) • (u₀ - s₀)

@[simp] theorem pplus_coord : pplus = ((1 / 2 : ℝ), (1 / 2 : ℝ)) := by
  apply Prod.ext <;> simp [pplus, u₀, s₀]

@[simp] theorem pminus_coord : pminus = ((1 / 2 : ℝ), (-(1 / 2) : ℝ)) := by
  apply Prod.ext <;> simp [pminus, u₀, s₀]

theorem pplus_add_pminus : pplus + pminus = u₀ := by
  apply Prod.ext <;> norm_num [u₀]

theorem pplus_sub_pminus : pplus - pminus = s₀ := by
  apply Prod.ext <;> norm_num [s₀]

theorem Q2_pplus : Q2 pplus = 0 := by simp [Q2]

theorem Q2_pminus : Q2 pminus = 0 := by simp [Q2]

section Idempotents

variable {μ : BiProd} (h : AdmissibleAt u₀ μ)

include h

/-- Idempotence of `p₊` is forced by the classification. -/
theorem mu_pplus_pplus : μ pplus pplus = pplus := by
  rw [fixedUnit_formula h]; apply Prod.ext <;> simp <;> norm_num

/-- Idempotence of `p₋` is forced by the classification. -/
theorem mu_pminus_pminus : μ pminus pminus = pminus := by
  rw [fixedUnit_formula h]; apply Prod.ext <;> simp <;> norm_num

/-- Orthogonality of the two candidate idempotents is forced by the classification. -/
theorem mu_pplus_pminus : μ pplus pminus = 0 := by
  rw [fixedUnit_formula h]
  apply Prod.ext <;> simp

theorem mu_pminus_pplus : μ pminus pplus = 0 := by
  rw [fixedUnit_formula h]
  apply Prod.ext <;> simp

end Idempotents

end NullSectorTask02
