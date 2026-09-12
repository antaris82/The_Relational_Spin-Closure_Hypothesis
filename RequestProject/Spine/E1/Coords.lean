import Mathlib
import RequestProject.Spine.E1.Hodge

/-!
# Task 11, Phase I : intrinsic real coordinates, matrices and determinants

This module supplies the small piece of linear-algebra engineering that Task 10 was
missing and that forced its shell branch to borrow the determinant of a spatial
reflection from the Hermitian comparison layer.

Everything here is defined from the **real** carrier `𝒮 = ℝ ⊕ ℝ³` alone:

* `SpinCore.coordEquiv : 𝒮 ≃ₗ[ℝ] (Fin 4 → ℝ)` — the frame of the spin factor
  (`FRAME_CHOICE`: a representational basis choice only, no new mathematical datum);
* `SpinCore.matOf F` — the matrix of a real-linear endomorphism in that frame, with
  `det_matOf : (matOf F).det = LinearMap.det F`;
* `SpinCore.gramB` — the Gram matrix of the intrinsic polarized form `B_𝒮` in that frame,
  and `BS_coord`;
* `det_sq_of_BS_preserving` — **intrinsic** proof that a `B_𝒮`-preserving endomorphism has
  determinant `±1` (Task 10 obtained this only by transport through `Herm₂(ℂ)`);
* `volS_eq_det` — the Task-10 volume form is the coordinate determinant, hence
  `volS_comp_linear : volS (L a) (L b) (L c) (L d) = det L * volS a b c d`.

No comparison module (`Task10Compare`, `Task10LieCompare`, `Herm2`, `Mink4`) is imported,
and — as the Phase-I audit verifies — no comparison constant occurs in the proof closure
of any theorem below.
-/

noncomputable section

namespace SpinCore

open SpinCore SpinCore Matrix

/-! ## Coordinates -/

/-- The coordinate vector of a carrier element in the intrinsic frame `(1, e₀, e₁, e₂)`. -/
def coordFun (x : LorentzCarrier) : Fin 4 → ℝ := ![x.1, x.2 0, x.2 1, x.2 2]

/-- The inverse coordinate map. -/
def uncoordFun (c : Fin 4 → ℝ) : LorentzCarrier := (c 0, ![c 1, c 2, c 3])

@[simp] theorem coordFun_zero (x : LorentzCarrier) : coordFun x 0 = x.1 := rfl
@[simp] theorem coordFun_one (x : LorentzCarrier) : coordFun x 1 = x.2 0 := rfl
@[simp] theorem coordFun_two (x : LorentzCarrier) : coordFun x 2 = x.2 1 := rfl
@[simp] theorem coordFun_three (x : LorentzCarrier) : coordFun x 3 = x.2 2 := rfl

/-- **FRAME_CHOICE.**  The intrinsic frame of the real carrier. -/
def coordEquiv : LorentzCarrier ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := coordFun
  map_add' x y := by
    funext i; fin_cases i <;> rfl
  map_smul' r x := by
    funext i; fin_cases i <;> rfl
  invFun := uncoordFun
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
  right_inv c := by
    funext i; fin_cases i <;> rfl

@[simp] theorem coordEquiv_apply (x : LorentzCarrier) : coordEquiv x = coordFun x := rfl

@[simp] theorem coordEquiv_symm_apply (c : Fin 4 → ℝ) : coordEquiv.symm c = uncoordFun c := rfl

@[simp] theorem coordFun_uncoordFun (c : Fin 4 → ℝ) : coordFun (uncoordFun c) = c := by
  funext i; fin_cases i <;> rfl

/-! ## Matrices -/

/-- The matrix of a real-linear endomorphism of the carrier in the intrinsic frame. -/
def matOf (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' ((coordEquiv : LorentzCarrier →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ F ∘ₗ
    ((coordEquiv.symm : (Fin 4 → ℝ) ≃ₗ[ℝ] LorentzCarrier) : (Fin 4 → ℝ) →ₗ[ℝ] LorentzCarrier))

/-- **The determinant is computed by the frame matrix.** -/
theorem det_matOf (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) : (matOf F).det = LinearMap.det F := by
  rw [matOf, LinearMap.det_toMatrix']
  exact LinearMap.det_conj F coordEquiv

theorem matOf_mulVec (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (x : LorentzCarrier) :
    matOf F *ᵥ coordFun x = coordFun (F x) := by
  rw [matOf, LinearMap.toMatrix'_mulVec]
  show coordFun (F (uncoordFun (coordFun x))) = _
  rw [show uncoordFun (coordFun x) = x from coordEquiv.symm_apply_apply x]

theorem matOf_entry (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (i j : Fin 4) :
    matOf F i j = coordFun (F (uncoordFun (Pi.single j 1))) i := rfl

/-- Every matrix entry is recovered by pairing with the standard basis vectors. -/
theorem entry_eq_dotProduct (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    A i j = (Pi.single i (1 : ℝ)) ⬝ᵥ (A *ᵥ Pi.single j 1) := by
  simp [Matrix.mulVec_single]

/-! ## The Gram matrix of `B_𝒮` -/

/-- The Gram matrix of the intrinsic polarized form in the intrinsic frame. -/
def gramB : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

theorem det_gramB : gramB.det = -1 := by
  simp [gramB, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem BS_coord (x y : LorentzCarrier) : BS x y = coordFun x ⬝ᵥ (gramB *ᵥ coordFun y) := by
  rw [BS_eq]
  simp [gramB, dotProduct, Matrix.mulVec, Fin.sum_univ_four, sip, coordFun]
  ring

/-- **B2 (key intrinsic lemma).**  A `B_𝒮`-preserving endomorphism satisfies the Gram
relation `Mᵀ G M = G`. -/
theorem gram_relation {F : LorentzCarrier →ₗ[ℝ] LorentzCarrier} (h : ∀ x y, BS (F x) (F y) = BS x y) :
    (matOf F)ᵀ * gramB * matOf F = gramB := by
  have key : ∀ c d : Fin 4 → ℝ,
      c ⬝ᵥ (((matOf F)ᵀ * gramB * matOf F) *ᵥ d) = c ⬝ᵥ (gramB *ᵥ d) := by
    intro c d
    have h1 : ((matOf F)ᵀ * gramB * matOf F) *ᵥ d
        = (matOf F)ᵀ *ᵥ (gramB *ᵥ (matOf F *ᵥ d)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have h2 : matOf F *ᵥ c = coordFun (F (uncoordFun c)) := by
      rw [← coordFun_uncoordFun c, matOf_mulVec, coordFun_uncoordFun]
    have h3 : matOf F *ᵥ d = coordFun (F (uncoordFun d)) := by
      rw [← coordFun_uncoordFun d, matOf_mulVec, coordFun_uncoordFun]
    rw [h2, h3]
    have := h (uncoordFun c) (uncoordFun d)
    rw [BS_coord, BS_coord, coordFun_uncoordFun, coordFun_uncoordFun] at this
    exact this
  ext i j
  rw [entry_eq_dotProduct ((matOf F)ᵀ * gramB * matOf F) i j,
    entry_eq_dotProduct gramB i j, key]

/-- **B2 (main intrinsic determinant dichotomy).**  Any real-linear endomorphism of the
carrier preserving the intrinsic polarized form has determinant `±1`.  Proved entirely
inside the real spin-factor model: no Hermitian carrier, no complex matrices. -/
theorem det_sq_of_BS_preserving {F : LorentzCarrier →ₗ[ℝ] LorentzCarrier} (h : ∀ x y, BS (F x) (F y) = BS x y) :
    (LinearMap.det F) ^ 2 = 1 := by
  have hg := congrArg Matrix.det (gram_relation h)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_matOf, det_gramB] at hg
  nlinarith [hg]

/-- Norm preservation implies `B_𝒮` preservation (the polarization identity). -/
theorem BS_of_NS_preserving {F : LorentzCarrier →ₗ[ℝ] LorentzCarrier} (h : ∀ x, NS (F x) = NS x) (x y : LorentzCarrier) :
    BS (F x) (F y) = BS x y := by
  unfold BS
  rw [← map_add, h, h, h]

/-- **B2 (intrinsic form of the Task-10 comparison lemma `det_sq_of_GLorWide`).** -/
theorem det_sq_of_NS_preserving {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (h : ∀ x, NS (F x) = NS x) :
    (LinearMap.det (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier)) ^ 2 = 1 :=
  det_sq_of_BS_preserving (BS_of_NS_preserving h)

/-! ## The volume form is the coordinate determinant -/

/-- The `4 × 4` coordinate matrix of four carrier elements. -/
def coordMat (a b c d : LorentzCarrier) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![coordFun a, coordFun b, coordFun c, coordFun d]

/-- **D1 (structure of the orientation datum).**  The Task-10 volume form is exactly the
determinant of the coordinate matrix in the intrinsic frame. -/
theorem volS_eq_det (a b c d : LorentzCarrier) : volS a b c d = (coordMat a b c d).det := by
  simp [volS, coordMat, coordFun, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem coordMat_comp (L : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (a b c d : LorentzCarrier) :
    coordMat (L a) (L b) (L c) (L d) = coordMat a b c d * (matOf L)ᵀ := by
  have key : ∀ (x : LorentzCarrier) (j : Fin 4),
      coordFun (L x) j = ∑ k, coordFun x k * (matOf L)ᵀ k j := by
    intro x j
    rw [← matOf_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  ext i j
  fin_cases i <;> simp [coordMat, Matrix.mul_apply, key]

/-- **D1 / K5 (exact orientation dependence).**  The volume form transforms by the
determinant: an orientation-reversing carrier automorphism reverses `volS`. -/
theorem volS_comp_linear (L : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (a b c d : LorentzCarrier) :
    volS (L a) (L b) (L c) (L d) = LinearMap.det L * volS a b c d := by
  rw [volS_eq_det, volS_eq_det, coordMat_comp, Matrix.det_mul, Matrix.det_transpose,
    det_matOf]
  ring

end SpinCore
