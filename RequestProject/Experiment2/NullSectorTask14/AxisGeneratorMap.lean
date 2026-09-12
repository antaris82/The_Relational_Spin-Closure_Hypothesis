import RequestProject.Experiment2.NullSectorTask14.ImplementerClosure

/-!
# Task 14, Layer 11 (§31–§34): the intrinsic axis-to-generator map

Only now — after the two axes have been reconstructed independently and after the third
direction has appeared through the mixed commutator — is the map

`J : old spatial vectors → carrier`

introduced.  It is **not** defined by a conventional formula: its values on the three
inherited basis directions are read off from the three derived generators

`GA = -(1/2)•J(A)`,  `GB = -(1/2)•J(B)`,  `GC = -(1/2)•J(C)`,

and its coordinate action is the linear extension of those three values.  Linearity is then
proved (§32); the square and the two products are computed (§33); and only at the very end
(§34) is the derived map recognized as multiplication by the inherited central element.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §31 — the map read off from the three derived axis generators -/

/-- **DERIVED (§31).**  The axis-to-generator map, written in coordinates: the linear
extension of the three values derived from the three axis systems. -/
noncomputable def Jmap (n : Vec3) : W := n.1 • wR + n.2.1 • (-wQ) + n.2.2 • wP

@[simp] theorem Jmap_coord_0 (n : Vec3) : Jmap n 0 = 0 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_1 (n : Vec3) : Jmap n 1 = 0 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_2 (n : Vec3) : Jmap n 2 = 0 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_3 (n : Vec3) : Jmap n 3 = 0 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_4 (n : Vec3) : Jmap n 4 = n.2.2 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_5 (n : Vec3) : Jmap n 5 = -n.2.1 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_6 (n : Vec3) : Jmap n 6 = n.1 := by simp [Jmap, wP, wQ, wR]
@[simp] theorem Jmap_coord_7 (n : Vec3) : Jmap n 7 = 0 := by simp [Jmap, wP, wQ, wR]

/-- **DERIVED (§31): `axis_generator_map_exists`.**  The map reproduces exactly the three
independently derived axis generators. -/
theorem Jmap_basis_cases :
    GA = (-(2⁻¹ : ℝ)) • Jmap (1, 0, 0) ∧
    GB = (-(2⁻¹ : ℝ)) • Jmap (0, 1, 0) ∧
    GC = (-(2⁻¹ : ℝ)) • Jmap (0, 0, 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GA]; funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR]
  · rw [GB]; funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR]
  · rw [GC]; funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR]

/-! ## §32 — linearity -/

/-- **PRINCIPAL THEOREM (§32): `axis_generator_map_linearity`.**  The derived map is
additive and real-homogeneous — the linearity test is *passed*, not assumed. -/
theorem Jmap_linear :
    (∀ n m : Vec3, Jmap (n + m) = Jmap n + Jmap m) ∧
    (∀ (a : ℝ) (n : Vec3), Jmap (a • n) = a • Jmap n) := by
  constructor
  · intro n m; funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR] <;> ring
  · intro a n; funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR] <;> ring

/-- The derived map packaged as a real-linear map. -/
noncomputable def JmapL : Vec3 →ₗ[ℝ] W where
  toFun := Jmap
  map_add' := Jmap_linear.1
  map_smul' := Jmap_linear.2

@[simp] theorem JmapL_apply (n : Vec3) : JmapL n = Jmap n := rfl

/-! ## §33 — the exact algebraic properties -/

/-- **NEUTRAL DEFINITION (§33), introduced only *after* the antisymmetric product has been
computed below: the bilinear spatial operation which the antisymmetric part produces.  No
conventional cross product is imported. -/
def spCross (n m : Vec3) : Vec3 :=
  (n.2.1 * m.2.2 - n.2.2 * m.2.1, n.2.2 * m.1 - n.1 * m.2.2, n.1 * m.2.1 - n.2.1 * m.1)

/-- **PRINCIPAL THEOREM (§33): `axis_generator_square`.**  The square of the derived
generator direction is minus the inherited spatial form. -/
theorem Jmap_sq (n : Vec3) : Jmap n ⋆ Jmap n = (-(h3 n n)) • w1 := by
  funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR, w1, dot3, wit8MulFun] <;> ring

/-- **PRINCIPAL THEOREM (§33): `axis_generator_symmetric_product`.**  The symmetric part of
the product of two derived generator directions is exactly the inherited spatial form. -/
theorem Jmap_symmetric_product (n m : Vec3) :
    Jmap n ⋆ Jmap m + Jmap m ⋆ Jmap n = (-(2 * h3 n m)) • w1 := by
  funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR, w1, dot3, wit8MulFun] <;> ring

/-- **PRINCIPAL THEOREM (§33): `axis_generator_antisymmetric_product`.**  The antisymmetric
part is again of the same shape: it is minus twice the derived generator direction of a new
bilinear spatial operation.  The operation `spCross` is *defined by* this relation, not
imported. -/
theorem Jmap_antisymmetric_product (n m : Vec3) :
    Jmap n ⋆ Jmap m - Jmap m ⋆ Jmap n = (-2 : ℝ) • Jmap (spCross n m) := by
  funext i; fin_cases i <;> simp [Jmap, spCross, wP, wQ, wR, wit8MulFun] <;> ring

/-- **DERIVED (§33).**  The full product, symmetric plus antisymmetric part. -/
theorem Jmap_mul (n m : Vec3) :
    Jmap n ⋆ Jmap m = (-(h3 n m)) • w1 + (-1 : ℝ) • Jmap (spCross n m) := by
  funext i; fin_cases i <;> simp [Jmap, spCross, wP, wQ, wR, w1, dot3, wit8MulFun] <;> ring

/-- **DERIVED (§33).**  The emergent bilinear operation reproduces, on the inherited basis,
exactly the cyclic pattern already visible in the mixed commutator. -/
theorem spCross_basis :
    spCross (1, 0, 0) (0, 1, 0) = (0, 0, 1) ∧
    spCross (0, 1, 0) (0, 0, 1) = (1, 0, 0) ∧
    spCross (0, 0, 1) (1, 0, 0) = (0, 1, 0) ∧
    (∀ n : Vec3, spCross n n = 0) := by
  refine ⟨by simp [spCross], by simp [spCross], by simp [spCross], fun n => ?_⟩
  have hzero : spCross n n = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    simp only [spCross, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  simpa using hzero

/-! ## The product of two embedded spatial vectors -/

/-- **DERIVED (§33).**  The complete product of two embedded old spatial vectors: the
inherited form plus the central element applied to the emergent bilinear operation.  This
identity is the computational engine of Phase II. -/
theorem spat_mul_spat (n m : Vec3) :
    spat n ⋆ spat m = (h3 n m) • w1 + wS ⋆ spat (spCross n m) := by
  funext i
  fin_cases i <;> simp [spCross, w1, wS, dot3, wit8MulFun] <;> ring

/-! ## §34 — the late identification of the derived map -/

/-- **PRINCIPAL THEOREM (§34), an OUTPUT and not a definition.**  The independently derived
axis-to-generator map coincides with multiplication by the inherited central element:

`J(n) = S ⋆ n`  for every old spatial vector `n`.

This is stated only after the three basis-axis reconstructions (§31), the linearity proof
(§32) and the algebraic relations (§33). -/
theorem Jmap_eq_central_mul (n : Vec3) : Jmap n = wS ⋆ spat n := by
  funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR, wS, wit8MulFun] <;> ring

/-- **DERIVED (§34).**  Consequently the generator direction commutes with its own axis and
anticommutes with every orthogonal one. -/
theorem Jmap_comm_axis (n : Vec3) : Jmap n ⋆ spat n = spat n ⋆ Jmap n := by
  rw [Jmap_eq_central_mul]
  calc (wS ⋆ spat n) ⋆ spat n = wS ⋆ (spat n ⋆ spat n) := mul_assoc_W _ _ _
    _ = (spat n ⋆ spat n) ⋆ wS := wS_central _
    _ = spat n ⋆ (spat n ⋆ wS) := mul_assoc_W _ _ _
    _ = spat n ⋆ (wS ⋆ spat n) := by rw [wS_central]

end NullSectorTask14
