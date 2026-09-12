import Mathlib
import RequestProject.Experiment1.Herm2

/-!
# Task 6, Sections 1–5 : the carrier as a canonical construction

Everything here starts from the *chosen* data `(M₂(ℂ), †)` and shows that the Hermitian
carrier, the acting group of units, the Hermitian / anti-Hermitian decomposition and the
positive cone are **canonical consequences** of that choice, not further independent choices.

Nothing here claims that `M₂(ℂ)` or the involution has been derived.
-/

noncomputable section

open Matrix Complex
open scoped ComplexOrder

namespace Carrier

/-- The ambient chosen `*`-algebra. -/
abbrev M2 : Type := Herm2.M2

/-! ## Section 1 : the Hermitian carrier is the fixed-point real form of the involution -/

/-- **Section 1.** The self-adjoint elements of `(M₂(ℂ), †)` are exactly the Hermitian
matrices used in the earlier tasks. -/
theorem selfAdjoint_eq_Herm (X : M2) : X ∈ selfAdjoint M2 ↔ X.IsHermitian :=
  (Matrix.isHermitian_iff_isSelfAdjoint).symm

/-- Set-level form of the same statement. -/
theorem selfAdjoint_set_eq_Herm :
    (selfAdjoint M2 : Set M2) = {H : M2 | H.IsHermitian} := by
  ext X; exact selfAdjoint_eq_Herm X

/-- The Hermitian carrier packaged as a real submodule of `M₂(ℂ)`: this is literally
Mathlib's `selfAdjoint` submodule of the fixed points of the involution. -/
abbrev Herm : Type := Herm2.Herm

/-! ## Section 2 : the canonical Hermitian / anti-Hermitian decomposition -/

/-- The Hermitian part `H_X = (X + X†)/2`. -/
def herPart (X : M2) : M2 := (2 : ℂ)⁻¹ • (X + Xᴴ)

/-- The second Hermitian component `K_X = (X - X†)/(2i)`. -/
def antiPart (X : M2) : M2 := (2 * Complex.I)⁻¹ • (X - Xᴴ)

theorem herPart_isHermitian (X : M2) : (herPart X).IsHermitian := by
  unfold Matrix.IsHermitian herPart
  rw [Matrix.conjTranspose_smul]
  simp [add_comm]

theorem antiPart_isHermitian (X : M2) : (antiPart X).IsHermitian := by
  unfold Matrix.IsHermitian antiPart
  rw [Matrix.conjTranspose_smul]
  have h : star ((2 * Complex.I)⁻¹) = -(2 * Complex.I)⁻¹ := by
    simp
  rw [h]
  simp [Matrix.conjTranspose_sub, neg_smul, smul_sub]
  module

/-- **Section 2.** `X = H_X + i K_X`. -/
theorem hermitian_decomposition (X : M2) :
    X = herPart X + Complex.I • antiPart X := by
  have hI : Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by field_simp
  rw [herPart, antiPart, smul_smul, hI]
  rw [← smul_add]
  have : (X + Xᴴ) + (X - Xᴴ) = (2 : ℂ) • X := by module
  rw [this, smul_smul]
  norm_num

/-- Uniqueness of the decomposition. -/
theorem hermitian_decomposition_unique {X H K H' K' : M2}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (hH' : H'.IsHermitian) (hK' : K'.IsHermitian)
    (h1 : X = H + Complex.I • K) (h2 : X = H' + Complex.I • K') :
    H = H' ∧ K = K' := by
  have hd : H - H' = Complex.I • (K' - K) := by
    have : H + Complex.I • K = H' + Complex.I • K' := by rw [← h1, ← h2]
    rw [smul_sub]
    linear_combination (norm := module) this
  have hdh : (H - H').IsHermitian := hH.sub hH'
  have hstar : (Complex.I • (K' - K))ᴴ = -(Complex.I • (K' - K)) := by
    rw [Matrix.conjTranspose_smul]
    have : ((K' - K)ᴴ) = K' - K := (hK'.sub hK)
    rw [this]
    simp [neg_smul]
  have h0 : H - H' = -(H - H') := by
    calc H - H' = (H - H')ᴴ := hdh.symm
      _ = (Complex.I • (K' - K))ᴴ := by rw [hd]
      _ = -(Complex.I • (K' - K)) := hstar
      _ = -(H - H') := by rw [hd]
  have hHH : H = H' := by
    have : (2 : ℂ) • (H - H') = 0 := by
      have := h0
      linear_combination (norm := module) this
    have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
    have := smul_eq_zero.1 this
    rcases this with h | h
    · exact absurd h h2ne
    · exact sub_eq_zero.1 h
  refine ⟨hHH, ?_⟩
  have : Complex.I • (K' - K) = 0 := by rw [← hd, hHH, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact absurd h Complex.I_ne_zero
  · exact (sub_eq_zero.1 h).symm

/-- The explicit real-linear equivalence `M₂(ℂ) ≃ℝ Herm × Herm`. -/
def decompEquiv : M2 ≃ₗ[ℝ] Herm × Herm where
  toFun X := (⟨herPart X, (Matrix.isHermitian_iff_isSelfAdjoint).1 (herPart_isHermitian X)⟩,
              ⟨antiPart X, (Matrix.isHermitian_iff_isSelfAdjoint).1 (antiPart_isHermitian X)⟩)
  map_add' X Y := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [herPart, antiPart, Matrix.conjTranspose_add] <;> module
  map_smul' r X := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [herPart, antiPart] <;> module
  invFun p := (p.1 : M2) + Complex.I • (p.2 : M2)
  left_inv X := (hermitian_decomposition X).symm
  right_inv p := by
    obtain ⟨⟨H, hH⟩, ⟨K, hK⟩⟩ := p
    have hH' : H.IsHermitian := (Matrix.isHermitian_iff_isSelfAdjoint).2 hH
    have hK' : K.IsHermitian := (Matrix.isHermitian_iff_isSelfAdjoint).2 hK
    set X : M2 := H + Complex.I • K with hX
    obtain ⟨e1, e2⟩ := hermitian_decomposition_unique (X := X)
      (herPart_isHermitian X) (antiPart_isHermitian X) hH' hK'
      (hermitian_decomposition X) hX
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

/-! ## Section 3 : the involution is determined by its fixed real form -/

/-- **Section 3.** A conjugate-linear additive map fixing every Hermitian matrix is the
conjugate transpose. -/
theorem star_unique_from_realForm (τ : M2 → M2)
    (hadd : ∀ X Y, τ (X + Y) = τ X + τ Y)
    (hsmul : ∀ (c : ℂ) (X : M2), τ (c • X) = (starRingEnd ℂ c) • τ X)
    (hfix : ∀ H : M2, H.IsHermitian → τ H = H) (X : M2) :
    τ X = Xᴴ := by
  have hdec := hermitian_decomposition X
  have hH := herPart_isHermitian X
  have hK := antiPart_isHermitian X
  calc τ X = τ (herPart X + Complex.I • antiPart X) := by rw [← hdec]
    _ = τ (herPart X) + τ (Complex.I • antiPart X) := hadd _ _
    _ = herPart X + (starRingEnd ℂ Complex.I) • τ (antiPart X) := by
        rw [hfix _ hH, hsmul]
    _ = herPart X - Complex.I • antiPart X := by
        rw [hfix _ hK]
        simp [neg_smul, sub_eq_add_neg]
    _ = Xᴴ := by
        conv_rhs => rw [hdec]
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH, hK]
        simp [neg_smul, sub_eq_add_neg]

/-! ## Section 4 : `GL(2,ℂ)` is the unit group of the ambient algebra -/

/-- **Section 4.** Mathlib's `GL (Fin 2) ℂ` *is* the group of units of `M₂(ℂ)`, definitionally. -/
theorem GL_eq_units : Matrix.GeneralLinearGroup (Fin 2) ℂ = M2ˣ := rfl

/-- The identity equivalence, recorded as a group isomorphism. -/
def GL_mulEquiv_units : Matrix.GeneralLinearGroup (Fin 2) ℂ ≃* M2ˣ := MulEquiv.refl _

/-- Membership form: a matrix underlies an element of `GL(2,ℂ)` iff it is a unit of the algebra. -/
theorem isUnit_iff_exists_GL (A : M2) :
    IsUnit A ↔ ∃ g : Matrix.GeneralLinearGroup (Fin 2) ℂ, (g : M2) = A := by
  constructor
  · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
  · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩

/-! ## Section 5 : the intrinsic positive cone -/

/-- The positive semidefinite cone inside the Hermitian carrier, defined by the intrinsic
matrix order (never by Minkowski coordinates). -/
def PSDCone : Set Herm := {H : Herm | ((H : M2)).PosSemidef}

/-- The positive definite interior. -/
def PDCone : Set Herm := {H : Herm | ((H : M2)).PosDef}

theorem one_isHermitian : (1 : M2).IsHermitian := Matrix.isHermitian_one

/-- The identity as an element of the carrier. -/
def oneH : Herm := ⟨1, (Matrix.isHermitian_iff_isSelfAdjoint).1 one_isHermitian⟩

/-- **Section 5.** `I` is positive definite, hence an interior point of the cone. -/
theorem one_mem_PDCone : oneH ∈ PDCone := Matrix.PosDef.one

theorem one_mem_PSDCone : oneH ∈ PSDCone := Matrix.PosDef.one.posSemidef

/-- **Section 5.** The congruence action preserves positive semidefiniteness, for arbitrary `A`. -/
theorem psd_congruence (A : M2) {H : M2} (h : H.PosSemidef) : (A * H * Aᴴ).PosSemidef :=
  h.mul_mul_conjTranspose_same A

theorem vecMul_injective_of_isUnit' {A : M2} (hA : IsUnit A) : Function.Injective A.vecMul :=
  Matrix.vecMul_injective_of_isUnit hA

theorem posDef_congruence {A : M2} (hA : IsUnit A) {H : M2} (h : H.PosDef) :
    (A * H * Aᴴ).PosDef :=
  h.mul_mul_conjTranspose_same (vecMul_injective_of_isUnit' hA)

/-- **Section 5.** For invertible `A`, positive semidefiniteness is *equivalent* to that of the
congruate. -/
theorem psd_congruence_iff {A : M2} (hA : IsUnit A) (H : M2) :
    H.PosSemidef ↔ (A * H * Aᴴ).PosSemidef := by
  refine ⟨fun h => psd_congruence A h, fun h => ?_⟩
  have hinv : IsUnit ((hA.unit⁻¹ : M2ˣ) : M2) := Units.isUnit _
  have := psd_congruence ((hA.unit⁻¹ : M2ˣ) : M2) h
  have hmul : ((hA.unit⁻¹ : M2ˣ) : M2) * (A * H * Aᴴ) * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ = H := by
    have h1 : ((hA.unit⁻¹ : M2ˣ) : M2) * A = 1 := by
      have : ((hA.unit⁻¹ : M2ˣ) : M2) * (hA.unit : M2) = 1 := by
        rw [← Units.val_mul]; simp
      rwa [hA.unit_spec] at this
    have h2 : Aᴴ * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc ((hA.unit⁻¹ : M2ˣ) : M2) * (A * H * Aᴴ) * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ
        = (((hA.unit⁻¹ : M2ˣ) : M2) * A) * H * (Aᴴ * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ) := by
          simp [Matrix.mul_assoc]
      _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  rwa [hmul] at this

/-- **Section 5.** Same equivalence for the positive definite cone. -/
theorem posDef_congruence_iff {A : M2} (hA : IsUnit A) (H : M2) :
    H.PosDef ↔ (A * H * Aᴴ).PosDef := by
  refine ⟨fun h => posDef_congruence hA h, fun h => ?_⟩
  have hinv : IsUnit ((hA.unit⁻¹ : M2ˣ) : M2) := Units.isUnit _
  have := posDef_congruence hinv h
  have h1 : ((hA.unit⁻¹ : M2ˣ) : M2) * A = 1 := by
    have : ((hA.unit⁻¹ : M2ˣ) : M2) * (hA.unit : M2) = 1 := by
      rw [← Units.val_mul]; simp
    rwa [hA.unit_spec] at this
  have h2 : Aᴴ * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hmul : ((hA.unit⁻¹ : M2ˣ) : M2) * (A * H * Aᴴ) * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ = H := by
    calc ((hA.unit⁻¹ : M2ˣ) : M2) * (A * H * Aᴴ) * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ
        = (((hA.unit⁻¹ : M2ˣ) : M2) * A) * H * (Aᴴ * (((hA.unit⁻¹ : M2ˣ) : M2))ᴴ) := by
          simp [Matrix.mul_assoc]
      _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  rwa [hmul] at this

end Carrier
