import RequestProject.Experiment2.NullSectorTask08.FullVec4Embedding

/-!
# Task 09, Layer 0: the inherited (safe) base and the neutral quadratic interface

## Import ledger (INHERITED)

The single import is `RequestProject.Experiment2.NullSectorTask08.FullVec4Embedding`.  In
particular

* `RequestProject.Experiment2.NullSectorTask08.Identification` — the Task-08 *late
  conventional identification* layer — is **not** imported here and is not
  reachable from any Task-09 reconstruction module.  It enters only in the very
  last comparison module `RequestProject.Experiment2.NullSectorTask09.Identification`.
* No Task-05 module is imported anywhere in the project.

Inherited Task-08 declarations actually used by Task 09:

* the carrier `Wit8` (renamed `W` below) and the bilinear product `wit8Mul`;
* the two-sided unit `w1` and the associativity theorem `wit8Mul_assoc`;
* the eight derived basis elements `w1, wA, wB, wC, wP, wQ, wR, wS` together
  with the derived multiplication table (`wit8_wA_wB`, … , `wit8_wS_wS`);
* the injective linear embedding `iota3 : Vec4 →ₗ[ℝ] W` of the complete old
  carrier, with `iota3_e₀`, `iota3_dirA`, `iota3_dirB`, `iota3_dirC`;
* the inherited old square law `iota3_oldSq`;
* the inherited Lorentz form `NullSectorTask01.Q4` with its old-carrier values
  `Q4_e₀`, `Q4_dirA`, `Q4_dirB`, `Q4_dirC`.

Nothing else from earlier tasks is used inside the Task-09 reconstruction core.

## Target-structure firewall

No determinant, reduced norm, Clifford norm, spinor norm, conjugation,
involution, reversion, adjoint, trace, characteristic polynomial, eigenvalue,
matrix type or complex scalar field appears in this module or in any Task-09
module before the final comparison layer.

## The neutral quadratic interface

`IsRealQuadratic N` is a transparent predicate: real homogeneity of degree two
together with real bilinearity of the polarization `polar N x y :=
N (x + y) - N x - N y`.  Multiplicativity is *not* part of it; the two
predicates are kept logically separate throughout.
-/

namespace NullSectorTask09

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08

/-! ## The Task-08 associative witness, under a neutral name -/

/-- **INHERITED.**  The Task-08 associative carrier. -/
abbrev W : Type := Wit8

/-- Notation for the inherited Task-08 product. -/
scoped infixl:70 " ⋆ " => wit8Mul

/-! ### Inherited structural facts (restated for readability) -/

theorem one_mul_W (x : W) : w1 ⋆ x = x := wit8Mul_one_left x

theorem mul_one_W (x : W) : x ⋆ w1 = x := wit8Mul_one_right x

theorem mul_assoc_W (x y z : W) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) := wit8Mul_assoc x y z

theorem mul_add_W (x y z : W) : x ⋆ (y + z) = x ⋆ y + x ⋆ z := by
  simp [map_add]

theorem add_mul_W (x y z : W) : (x + y) ⋆ z = x ⋆ z + y ⋆ z := by
  simp [map_add]

theorem mul_smul_W (r : ℝ) (x y : W) : x ⋆ (r • y) = r • (x ⋆ y) := by
  simp [map_smul]

theorem smul_mul_W (r : ℝ) (x y : W) : (r • x) ⋆ y = r • (x ⋆ y) := by
  simp [map_smul]

theorem mul_neg_W (x y : W) : x ⋆ (-y) = -(x ⋆ y) := map_neg (wit8Mul x) y

theorem neg_mul_W (x y : W) : (-x) ⋆ y = -(x ⋆ y) := by
  rw [map_neg]; rfl

theorem mul_zero_W (x : W) : x ⋆ (0 : W) = 0 := map_zero (wit8Mul x)

theorem zero_mul_W (x : W) : (0 : W) ⋆ x = 0 := by
  rw [map_zero]; rfl

/-- **INHERITED.**  The derived central element squares to `-1`. -/
theorem wS_sq : wS ⋆ wS = - w1 := wit8_wS_wS

/-- **INHERITED (DERIVED IN TASK 08).**  `S` commutes with every element of the
eight-dimensional closure.  Re-verified here directly on the witness carrier
from the inherited coefficient law. -/
theorem wS_central (x : W) : wS ⋆ x = x ⋆ wS := by
  funext i; fin_cases i <;> simp [wS]

/-! ### Inherited old-carrier data -/

theorem iota3_add (X Y : Vec4) : iota3 (X + Y) = iota3 X + iota3 Y := map_add _ _ _

theorem Q4_dirA_add_dirB : Q4 (dirA + dirB) = -2 := by
  rw [(dir_coords).1, (dir_coords).2.1]; norm_num [Q4]

theorem Q4_dirA_add_dirC : Q4 (dirA + dirC) = -2 := by
  rw [(dir_coords).1, (dir_coords).2.2]; norm_num [Q4]

theorem Q4_dirB_add_dirC : Q4 (dirB + dirC) = -2 := by
  rw [(dir_coords).2.1, (dir_coords).2.2]; norm_num [Q4]

theorem Q4_e₀_add_dirA : Q4 (e₀ + dirA) = 0 := by
  rw [(dir_coords).1]; norm_num [Q4, e₀]

theorem Q4_e₀_add_dirB : Q4 (e₀ + dirB) = 0 := by
  rw [(dir_coords).2.1]; norm_num [Q4, e₀]

theorem Q4_e₀_add_dirC : Q4 (e₀ + dirC) = 0 := by
  rw [(dir_coords).2.2]; norm_num [Q4, e₀]

/-! ## The neutral quadratic-map interface -/

variable {V : Type*} [AddCommGroup V]

/-- **DERIVED INTERFACE.**  The polarization of a map on the carrier. -/
def polar (N : W → V) (x y : W) : V := N (x + y) - N x - N y

variable [Module ℝ V]

/-- **DERIVED INTERFACE.**  `N` is *real-quadratic*: it is homogeneous of degree
two for real scalars and its polarization is real-bilinear.  Multiplicativity is
deliberately **not** part of this predicate. -/
structure IsRealQuadratic (N : W → V) : Prop where
  /-- Degree-two real homogeneity. -/
  homog : ∀ (r : ℝ) (x : W), N (r • x) = (r ^ 2) • N x
  /-- Additivity of the polarization in its first argument. -/
  polar_add_left : ∀ x y z : W, polar N (x + y) z = polar N x z + polar N y z
  /-- Real homogeneity of the polarization in its first argument. -/
  polar_smul_left : ∀ (r : ℝ) (x y : W), polar N (r • x) y = r • polar N x y

namespace IsRealQuadratic

variable {N : W → V}

omit [Module ℝ V] in
/-- The polarization is symmetric by construction. -/
theorem polar_comm (x y : W) : polar N x y = polar N y x := by
  simp only [polar, add_comm x y]
  abel

theorem map_zero (h : IsRealQuadratic N) : N 0 = 0 := by
  have := h.homog 0 0
  simpa using this

theorem polar_add_right (h : IsRealQuadratic N) (x y z : W) :
    polar N x (y + z) = polar N x y + polar N x z := by
  rw [polar_comm, h.polar_add_left, polar_comm (N := N) y x, polar_comm (N := N) z x]

theorem polar_smul_right (h : IsRealQuadratic N) (r : ℝ) (x y : W) :
    polar N x (r • y) = r • polar N x y := by
  rw [polar_comm, h.polar_smul_left, polar_comm (N := N) y x]

/-- The diagonal of the polarization is twice the map. -/
theorem polar_self (h : IsRealQuadratic N) (x : W) : polar N x x = (2 : ℝ) • N x := by
  have hx : x + x = (2 : ℝ) • x := by module
  have h4 : N (x + x) = (4 : ℝ) • N x := by
    rw [hx, h.homog]; norm_num
  simp only [polar, h4]
  module

/-- **A map satisfying the interface is completely determined by its
polarization.** -/
theorem eq_half_polar (h : IsRealQuadratic N) (x : W) :
    N x = ((2 : ℝ)⁻¹) • polar N x x := by
  rw [h.polar_self, smul_smul]
  norm_num

theorem polar_neg_left (h : IsRealQuadratic N) (x y : W) :
    polar N (-x) y = - polar N x y := by
  have hx : (-x : W) = ((-1 : ℝ)) • x := by module
  rw [hx, h.polar_smul_left]
  module

theorem polar_neg_right (h : IsRealQuadratic N) (x y : W) :
    polar N x (-y) = - polar N x y := by
  rw [polar_comm, h.polar_neg_left, polar_comm (N := N) y x]

/-- The polarization packaged as an honest real-bilinear map. -/
def polarBil (h : IsRealQuadratic N) : W →ₗ[ℝ] W →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ (polar N) h.polar_add_left h.polar_smul_left
    h.polar_add_right h.polar_smul_right

@[simp] theorem polarBil_apply (h : IsRealQuadratic N) (x y : W) :
    h.polarBil x y = polar N x y := rfl

end IsRealQuadratic

/-! ## The multiplicativity and restriction predicates, real codomain -/

/-- **MULTIPLICATIVE (real codomain).** -/
def MultiplicativeR (NR : W → ℝ) : Prop := ∀ x y : W, NR (x ⋆ y) = NR x * NR y

/-- **OLD-`Q4` RESTRICTION (real codomain).** -/
def ExtendsQ4R (NR : W → ℝ) : Prop := ∀ X : Vec4, NR (iota3 X) = Q4 X

end NullSectorTask09
