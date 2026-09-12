import Mathlib
import RequestProject.Spine.E1.LorentzClifford

/-!
# Task 11, Phase IV, obligation E3 : the pseudoscalar acts as the Hodge star

With `ι : Λ²𝒮 → Cl₃(ℝ)` from `Task11LorentzClifford.lean` (built from the universal even
Clifford construction) and `ω = e₀e₁e₂` the Task-9 central pseudoscalar, the critical
equation is tested and **decided**:

`SpinCore.iota_hodgeStar :  ι(⋆α) = -(ω · ι(α))`   for all `α ∈ Λ²𝒮`.

So the answer to E3 is *equality with a globally fixed minus sign* in the conventions
actually used by the project (Mathlib's `ι(v)² = +Q(v)`, the Task-9 orientation
`ω = e₀e₁e₂`, the Task-10 volume form `volS`, and the antisymmetrisation
`ι(x∧y) = ½(A(x)Ā(y) - A(y)Ā(x))`).  Equivalently

`SpinCore.iota_intertwines : ι(⋆α) = (-ω) · ι(α)`,

i.e. `ι` intertwines the Hodge complex structure `⋆` with multiplication by the central
square root of `-1` given by `-ω`.  Since `ω` and `-ω` are exactly the two central square
roots of `-1` (Task 9), the sign is *not* removable by any choice other than reversing the
Task-9 orientation; it is fixed once the conventions above are fixed.

`SpinCore.iota_injective` shows that `ι` is injective, so the identification of `Λ²𝒮` with
the vector-plus-bivector part of `Cl₃(ℝ)` is faithful.  Injectivity is proved by evaluating
in one faithful real `4 × 4` representation of the Clifford relations; that representation
is a *proof device* (a frame choice) and is used nowhere in the definition of `ι` or in the
statement of the bridge.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

open SpinCore

/-! ## Values of `ι` on the frame -/

@[simp] theorem spinToCl_one : spinToCl sOne = 1 := by
  show algebraMap ℝ Cl3 (1:ℝ) + ι q3 0 = 1
  simp

@[simp] theorem spinToClBar_one : spinToClBar sOne = 1 := by
  show algebraMap ℝ Cl3 (1:ℝ) - ι q3 0 = 1
  simp

@[simp] theorem spinToCl_bvec (i : Fin 3) : spinToCl (bvec i) = cle i := by
  show algebraMap ℝ Cl3 (0:ℝ) + ι q3 (evec i) = cle i
  simp [cle]

@[simp] theorem spinToClBar_bvec (i : Fin 3) : spinToClBar (bvec i) = -cle i := by
  show algebraMap ℝ Cl3 (0:ℝ) - ι q3 (evec i) = -cle i
  simp [cle]

theorem iota_one_bvec (i : Fin 3) : iota (wedge sOne (bvec i)) = -cle i := by
  rw [iota_wedge, iotaFun]
  simp only [spinToCl_one, spinToClBar_one, spinToCl_bvec, spinToClBar_bvec, one_mul,
    mul_one]
  module

theorem iota_bvec_bvec {i j : Fin 3} (h : i ≠ j) :
    iota (wedge (bvec i) (bvec j)) = -(cle i * cle j) := by
  rw [iota_wedge, iotaFun]
  simp only [spinToCl_bvec, spinToClBar_bvec, mul_neg]
  rw [cle_anticomm (Ne.symm h)]
  module

/-! ## `ι` in the `zmap` frame -/

theorem iota_zmap (c : Fin 6 → ℝ) :
    iota (zmap c) = c 0 • cle 0 + c 1 • cle 1 + c 2 • cle 2
      - c 3 • (cle 0 * cle 1) - c 4 • (cle 0 * cle 2) - c 5 • (cle 1 * cle 2) := by
  rw [zmap_apply_eq]
  simp only [map_add, map_smul, map_neg, iota_one_bvec,
    iota_bvec_bvec (show (0 : Fin 3) ≠ 1 by decide),
    iota_bvec_bvec (show (0 : Fin 3) ≠ 2 by decide),
    iota_bvec_bvec (show (1 : Fin 3) ≠ 2 by decide)]
  module

/-! ## The pseudoscalar acting on the frame

The six products below are computed with the word-sorting rewriting system installed in
Task 9 (`s10, s20, s21, t10, t20, t21, cle_sq, cle_sq_mul`).
-/

theorem omega_mul_cle0 : omega * cle 0 = cle 1 * cle 2 := by
  simp only [omega_assoc, mul_assoc, s10, t20, cle_sq_mul, mul_neg, neg_neg]

theorem omega_mul_cle1 : omega * cle 1 = -(cle 0 * cle 2) := by
  simp only [omega_assoc, mul_assoc, t21, cle_sq_mul, mul_neg]

theorem omega_mul_cle2 : omega * cle 2 = cle 0 * cle 1 := by
  simp only [omega_assoc, mul_assoc, cle_sq, mul_one]

theorem omega_mul_cle01 : omega * (cle 0 * cle 1) = -cle 2 := by
  simp only [omega_assoc, mul_assoc, s10, s20, t21, cle_sq_mul, mul_neg, neg_neg]

theorem omega_mul_cle02 : omega * (cle 0 * cle 2) = cle 1 := by
  simp only [omega_assoc, mul_assoc, s20, t10, cle_sq_mul, cle_sq, mul_neg, neg_neg,
    mul_one]

theorem omega_mul_cle12 : omega * (cle 1 * cle 2) = -cle 0 := by
  simp only [omega_assoc, mul_assoc, s21, cle_sq, mul_neg, mul_one]

/-! ## E3 : the bridge -/

/-- **E3 (main).**  The Hodge operator on bivectors is implemented, through `ι`, by
multiplication by the Task-9 central pseudoscalar, with a globally fixed minus sign:
`ι(⋆α) = -(ω · ι(α))`. -/
theorem iota_hodgeStar (z : ⋀[ℝ]^2 LorentzCarrier) : iota (hodgeStar z) = -(omega * iota z) := by
  obtain ⟨c, rfl⟩ := zmap_surjective z
  rw [hodgeStar_zmap, iota_zmap, iota_zmap]
  simp only [hodgeCoord_0, hodgeCoord_1, hodgeCoord_2, hodgeCoord_3, hodgeCoord_4,
    hodgeCoord_5, mul_add, mul_sub, mul_smul_comm, omega_mul_cle0, omega_mul_cle1,
    omega_mul_cle2, omega_mul_cle01, omega_mul_cle02, omega_mul_cle12]
  module

/-- **E3 (restatement).**  `ι` intertwines `⋆` with multiplication by the central square
root of `-1` given by `-ω`. -/
theorem iota_intertwines (z : ⋀[ℝ]^2 LorentzCarrier) : iota (hodgeStar z) = (-omega) * iota z := by
  rw [iota_hodgeStar, neg_mul]

/-- `-ω` is again a central square root of `-1`. -/
theorem neg_omega_sq : (-omega) * (-omega) = -1 := by
  rw [neg_mul_neg, omega_sq]

/-! ## Injectivity of `ι`

A faithful real `4 × 4` representation of the three Clifford generators.  It is used only
to prove injectivity; neither `ι` nor the bridge theorem mentions it. -/

/-- Real `4 × 4` matrices satisfying the Clifford relations of `q3`. -/
def repA : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ
  | 0 => Matrix.of ![![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0]]
  | 1 => Matrix.of ![![0, 0, 0, 1], ![0, 0, -1, 0], ![0, -1, 0, 0], ![1, 0, 0, 0]]
  | 2 => Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

/-- The linear map `ℝ³ → M₄(ℝ)` sending the basis to `repA`. -/
def repLin : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun v := v 0 • repA 0 + v 1 • repA 1 + v 2 • repA 2
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

theorem repLin_sq (v : Fin 3 → ℝ) :
    repLin v * repLin v = algebraMap ℝ (Matrix (Fin 4) (Fin 4) ℝ) (q3 v) := by
  show (v 0 • repA 0 + v 1 • repA 1 + v 2 • repA 2)
      * (v 0 • repA 0 + v 1 • repA 1 + v 2 • repA 2) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [repA, Matrix.mul_apply, Fin.sum_univ_succ, sip,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal] <;> ring

/-- The induced algebra map `Cl₃(ℝ) → M₄(ℝ)`. -/
def repCl : Cl3 →ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  CliffordAlgebra.lift q3 ⟨repLin, repLin_sq⟩

@[simp] theorem repCl_cle (i : Fin 3) : repCl (cle i) = repA i := by
  rw [cle, repCl, CliffordAlgebra.lift_ι_apply]
  show (evec i) 0 • repA 0 + (evec i) 1 • repA 1 + (evec i) 2 • repA 2 = repA i
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [evec, repA]

/-- The six frame elements of `ι`'s image are linearly independent. -/
theorem iota_zmap_eq_zero (c : Fin 6 → ℝ) (h : iota (zmap c) = 0) : c = 0 := by
  rw [iota_zmap] at h
  have hm := congrArg repCl h
  simp only [map_sub, map_add, map_smul, map_mul, map_zero, repCl_cle] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  have e03 := congrFun (congrFun hm 0) 3
  have e20 := congrFun (congrFun hm 2) 0
  have e21 := congrFun (congrFun hm 2) 1
  simp only [repA, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.of_apply, Matrix.zero_apply, Fin.sum_univ_succ, Fin.isValue, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at e00 e01 e02 e03 e20 e21
  funext i
  fin_cases i <;> simp at e00 e01 e02 e03 e20 e21 ⊢ <;> linarith

/-- **E2 (faithfulness).**  `ι : Λ²𝒮 → Cl₃(ℝ)` is injective. -/
theorem iota_injective : Function.Injective iota := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := zmap_surjective z
  rw [iota_zmap_eq_zero c hz]
  simp

end SpinCore
