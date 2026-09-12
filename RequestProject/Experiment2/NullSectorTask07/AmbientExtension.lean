import RequestProject.Experiment2.NullSectorTask07.SafeBase

/-!
# Task 07, Layer 1: the ambient extension

Exactly one assumption of Task 06 is opened here: products of embedded vectors
are no longer required to stay inside the embedded copy of the original
carrier.  Everything else is retained.

The ambient carrier `E` is an **arbitrary** real vector space.  No dimension,
basis, grading, involution, conjugation, norm, orientation or commutativity is
assumed, and no known algebraic structure is imported.  The assumed data are:

* a real bilinear product `mul : E →ₗ[ℝ] E →ₗ[ℝ] E`;
* associativity of that product;
* a two-sided unit `oneE`;
* an injective real-linear embedding `iota : Vec4 →ₗ[ℝ] E` with `iota e₀ = oneE`;
* `PreservesOldSquares`: every embedded original vector keeps its inherited
  square, `mul (iota X) (iota X) = iota (oldSq X)`.

`PreservesOldSquares` is **not** a new Task-07 assumption: `oldSq` is the
diagonal that the complete family of longitudinal `1+1` sectors already forces
on every sector-compatible product (`SafeBase.sectorCompatible_sq`).

`iota (Vec4)` is *not* assumed to be closed under `mul`.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Neutral predicates -/

/-- Associativity of a bilinear product on `E`. -/
def AssociativeE (mul : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop :=
  ∀ x y z : E, mul (mul x y) z = mul x (mul y z)

/-- `u` is a two-sided unit for a bilinear product on `E`. -/
def TwoSidedUnitE (mul : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) : Prop :=
  (∀ x : E, mul u x = x) ∧ (∀ x : E, mul x u = x)

/-- **Retention of the inherited diagonal law.**  Every embedded original vector
keeps the square already forced by the longitudinal sectors. -/
def PreservesOldSquares (mul : E →ₗ[ℝ] E →ₗ[ℝ] E) (emb : Vec4 →ₗ[ℝ] E) : Prop :=
  ∀ X : Vec4, mul (emb X) (emb X) = emb (oldSq X)

/-! ## The ambient extension datum -/

/-- **INPUT.**  An associative unital real bilinear extension of the original
carrier retaining the inherited square law.  Nothing else is assumed; in
particular the image of `iota` is *not* assumed to be closed under `mul`. -/
structure AmbientExt (E : Type*) [AddCommGroup E] [Module ℝ E] where
  /-- the ambient bilinear product -/
  mul : E →ₗ[ℝ] E →ₗ[ℝ] E
  /-- the two-sided unit -/
  oneE : E
  /-- associativity (the property Task 07 insists on) -/
  assoc : AssociativeE mul
  /-- `oneE` is a two-sided unit -/
  unit : TwoSidedUnitE mul oneE
  /-- the embedding of the original carrier -/
  iota : Vec4 →ₗ[ℝ] E
  /-- the embedding is injective -/
  iota_inj : Function.Injective iota
  /-- the normalized future unit becomes the ambient unit -/
  iota_e₀ : iota e₀ = oneE
  /-- the inherited square law is retained -/
  oldsq : PreservesOldSquares mul iota

namespace AmbientExt

variable (S : AmbientExt E)

@[simp] theorem one_mul' (x : E) : S.mul S.oneE x = x := S.unit.1 x

@[simp] theorem mul_one' (x : E) : S.mul x S.oneE = x := S.unit.2 x

theorem mul_assoc' (x y z : E) : S.mul (S.mul x y) z = S.mul x (S.mul y z) := S.assoc x y z

theorem sq_iota (X : Vec4) : S.mul (S.iota X) (S.iota X) = S.iota (oldSq X) := S.oldsq X

/-- The ambient unit is nonzero: otherwise `iota` would kill `e₀`. -/
theorem oneE_ne_zero : S.oneE ≠ 0 := by
  intro h0
  have h1 : S.iota e₀ = S.iota 0 := by rw [S.iota_e₀, h0, map_zero]
  have h2 : (e₀ : Vec4) = 0 := S.iota_inj h1
  have := congrArg (fun X : Vec4 => X.1) h2
  simp [e₀] at this

end AmbientExt

end NullSectorTask07
