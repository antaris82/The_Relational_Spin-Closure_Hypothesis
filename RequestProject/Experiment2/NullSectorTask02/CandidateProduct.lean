import RequestProject.Experiment2.NullSectorTask02.LorentzData

/-!
# Task 02, Layer 2: unknown bilinear products on the longitudinal carrier

An unknown real bilinear product is carried by `LinearMap.BilinMap ℝ Long Long`;
bilinearity is therefore part of the carrier and is never an extra hypothesis.

Only the following predicates are defined here:
left/right/two-sided unit, `Q2`-multiplicativity, commutativity, associativity,
and the admissibility condition

`AdmissibleAt e μ := TwoSidedUnit μ e ∧ QMultiplicative μ`.

Commutativity and associativity are deliberately **not** part of admissibility;
they are tested later as possible consequences.

Also proved here: the necessary conditions on a unit (`Q2 e = 1`) and the
uniqueness of a two-sided unit for a fixed product.
-/

namespace NullSectorTask02

open NullSectorTask01

/-- Carrier of an unknown real bilinear product on `Long`. -/
abbrev BiProd : Type := LinearMap.BilinMap ℝ Long Long

/-- `e` is a left unit for `μ`. -/
def LeftUnit (μ : BiProd) (e : Long) : Prop := ∀ X, μ e X = X

/-- `e` is a right unit for `μ`. -/
def RightUnit (μ : BiProd) (e : Long) : Prop := ∀ X, μ X e = X

/-- `e` is a two-sided unit for `μ`. -/
def TwoSidedUnit (μ : BiProd) (e : Long) : Prop := LeftUnit μ e ∧ RightUnit μ e

/-- `μ` is multiplicative for the quadratic form `Q2`. -/
def QMultiplicative (μ : BiProd) : Prop := ∀ X Y, Q2 (μ X Y) = Q2 X * Q2 Y

/-- `μ` is commutative. -/
def Commutative (μ : BiProd) : Prop := ∀ X Y, μ X Y = μ Y X

/-- `μ` is associative. -/
def Associative (μ : BiProd) : Prop := ∀ X Y Z, μ (μ X Y) Z = μ X (μ Y Z)

/-- Main admissibility condition: a two-sided unit `e` and `Q2`-multiplicativity.
No commutativity, associativity, or any coordinate formula is assumed. -/
def AdmissibleAt (e : Long) (μ : BiProd) : Prop := TwoSidedUnit μ e ∧ QMultiplicative μ

/-- Weakened admissibility: only a *left* unit is required. -/
def LeftAdmissibleAt (e : Long) (μ : BiProd) : Prop := LeftUnit μ e ∧ QMultiplicative μ

theorem AdmissibleAt.toLeft {e : Long} {μ : BiProd} (h : AdmissibleAt e μ) :
    LeftAdmissibleAt e μ := ⟨h.1.1, h.2⟩

/-- Bilinear expansion of an arbitrary product in the chosen coordinate basis. -/
theorem bilin_expand (μ : BiProd) (X Y : Long) :
    μ X Y = (X.1 * Y.1) • μ u₀ u₀ + (X.1 * Y.2) • μ u₀ s₀
      + (X.2 * Y.1) • μ s₀ u₀ + (X.2 * Y.2) • μ s₀ s₀ := by
  conv_lhs => rw [coord_decomp X, coord_decomp Y]
  simp [map_add, map_smul, smul_add, smul_smul, add_assoc, mul_comm]
  abel

/-- **Derived, not assumed.**  A left unit of a `Q2`-multiplicative product
necessarily has `Q2 e = 1`.  (Right units are not needed for this.) -/
theorem Q2_leftUnit_eq_one {e : Long} {μ : BiProd} (h : LeftAdmissibleAt e μ) : Q2 e = 1 := by
  have h1 : Q2 (μ e u₀) = Q2 e * Q2 u₀ := h.2 e u₀
  rw [h.1 u₀] at h1
  simpa using h1.symm

/-- Consequently `e ≠ 0` for a left unit of a `Q2`-multiplicative product. -/
theorem leftUnit_ne_zero {e : Long} {μ : BiProd} (h : LeftAdmissibleAt e μ) : e ≠ 0 := by
  intro he
  have := Q2_leftUnit_eq_one h
  rw [he] at this
  simp [Q2] at this

theorem Q2_unit_eq_one {e : Long} {μ : BiProd} (h : AdmissibleAt e μ) : Q2 e = 1 :=
  Q2_leftUnit_eq_one h.toLeft

/-- Uniqueness of a two-sided unit for a fixed product, from the unit laws alone. -/
theorem twoSidedUnit_unique {μ : BiProd} {e e' : Long}
    (h : TwoSidedUnit μ e) (h' : TwoSidedUnit μ e') : e = e' := by
  have h1 : μ e e' = e' := h.1 e'
  have h2 : μ e e' = e := h'.2 e
  rw [← h1, h2]

/-- A two-sided unit is unique also when the second one is only assumed to be a left
unit and the first only a right unit. -/
theorem unit_unique_mixed {μ : BiProd} {e e' : Long}
    (h : LeftUnit μ e) (h' : RightUnit μ e') : e = e' := by
  have h1 : μ e e' = e' := h e'
  have h2 : μ e e' = e := h' e
  rw [← h1, h2]

end NullSectorTask02
