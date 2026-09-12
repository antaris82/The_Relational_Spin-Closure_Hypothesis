import Mathlib
import RequestProject.Experiment1.Task6Cone
import RequestProject.Experiment1.DetPreservingQuotient

/-!
# Task 6, Sections 8–9 : the intrinsic carrier automorphism group

`Aut⁺_{det,𝒫}(A_sa)` is defined using *carrier data only*: real-linear automorphisms of the
Hermitian carrier preserving the determinant, the positive semidefinite cone, and the real
orientation.  It is proved to be a group, isomorphic to the independently defined `SO⁺(1,3)`,
and the Task 5 effective congruence group `G_det/U(1)` is mapped onto it directly by
`[A] ↦ (H ↦ A H Aᴴ)`.
-/

noncomputable section

open Matrix Complex Mink4 Herm2 SpinLorentz
open scoped ComplexOrder

namespace Carrier

/-! ## Transport of a carrier automorphism to a real `4 × 4` matrix -/

/-- The coordinate form of a real-linear automorphism of the Hermitian carrier. -/
def coordEquivOf (F : Herm ≃ₗ[ℝ] Herm) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  hermCoordEquiv.trans (F.trans hermCoordEquiv.symm)

/-- The real `4 × 4` matrix of a carrier automorphism. -/
def matOf (F : Herm ≃ₗ[ℝ] Herm) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (coordEquivOf F : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))

theorem matOf_mulVec (F : Herm ≃ₗ[ℝ] Herm) (v : Fin 4 → ℝ) :
    matOf F *ᵥ v = coordsOf ((F (hermCoordEquiv v) : Herm) : M2) := by
  rw [matOf, LinearMap.toMatrix'_mulVec]
  rfl

theorem hermCoordEquiv_matOf_mulVec (F : Herm ≃ₗ[ℝ] Herm) (v : Fin 4 → ℝ) :
    hermCoordEquiv (matOf F *ᵥ v) = F (hermCoordEquiv v) := by
  rw [matOf_mulVec]
  exact hermCoordEquiv.apply_symm_apply _

theorem matOf_one : matOf 1 = 1 := by
  have h : coordEquivOf 1 = LinearEquiv.refl ℝ (Fin 4 → ℝ) := by
    ext v i
    show coordsOf (((1 : Herm ≃ₗ[ℝ] Herm) (hermCoordEquiv v) : Herm) : M2) i = v i
    show coordsOf ((hermCoordEquiv v : Herm) : M2) i = v i
    have : coordsOf ((hermCoordEquiv v : Herm) : M2) = v := hermCoordEquiv.symm_apply_apply v
    rw [this]
  rw [matOf, h]
  simp [LinearMap.toMatrix'_id]

theorem matOf_mul (F G : Herm ≃ₗ[ℝ] Herm) : matOf (F * G) = matOf F * matOf G := by
  have h : (coordEquivOf (F * G) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
      = (coordEquivOf F : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ
        (coordEquivOf G : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) := by
    apply LinearMap.ext
    intro v
    show coordEquivOf (F * G) v = coordEquivOf F (coordEquivOf G v)
    simp only [coordEquivOf, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [matOf, matOf, matOf, h, LinearMap.toMatrix'_comp]

theorem matOf_injective : Function.Injective matOf := by
  intro F G h
  have h1 : (coordEquivOf F : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
      = (coordEquivOf G : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) := by
    have := congrArg Matrix.toLin' h
    simpa [matOf, Matrix.toLin'_toMatrix'] using this
  apply LinearEquiv.ext
  intro H
  have h2 : coordEquivOf F (hermCoordEquiv.symm H) = coordEquivOf G (hermCoordEquiv.symm H) :=
    congrFun (congrArg DFunLike.coe h1) (hermCoordEquiv.symm H)
  simp only [coordEquivOf, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h2
  have h3 := congrArg hermCoordEquiv h2
  rw [hermCoordEquiv.apply_symm_apply, hermCoordEquiv.apply_symm_apply] at h3
  exact h3

/-- The determinant of the transported matrix is the real determinant of the carrier map. -/
theorem det_matOf (F : Herm ≃ₗ[ℝ] Herm) :
    (matOf F).det = LinearMap.det (F : Herm →ₗ[ℝ] Herm) := by
  rw [matOf, LinearMap.det_toMatrix']
  have : (coordEquivOf F : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
      = (hermCoordEquiv.symm : Herm ≃ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ (F : Herm →ₗ[ℝ] Herm) ∘ₗ
        ((hermCoordEquiv.symm).symm : (Fin 4 → ℝ) →ₗ[ℝ] Herm) := by
    apply LinearMap.ext; intro v; rfl
  rw [this, LinearMap.det_conj]

/-- The determinant of a Hermitian matrix in terms of its coordinates. -/
theorem det_coe_hermCoordEquiv (v : Fin 4 → ℝ) :
    ((hermCoordEquiv v : Herm) : M2).det = ((Q4 v : ℝ) : ℂ) := det_coords v

theorem det_eq_Q4_coords (H : Herm) : ((H : M2)).det = ((Q4 (coordsOf (H : M2)) : ℝ) : ℂ) := by
  have : hermCoordEquiv (coordsOf (H : M2)) = H := hermCoordEquiv.apply_symm_apply H
  conv_lhs => rw [← this]
  exact det_coords _

/-! ## Section 8 : the intrinsic group `Aut⁺_{det,𝒫}` -/

/-- The three intrinsic conditions: determinant preservation, positive-cone preservation
(both ways), and real orientation `+1`. -/
def IsDetConeAut (F : Herm ≃ₗ[ℝ] Herm) : Prop :=
  (∀ H : Herm, ((F H : Herm) : M2).det = ((H : Herm) : M2).det) ∧
  (∀ H : Herm, ((H : M2)).PosSemidef ↔ ((F H : Herm) : M2).PosSemidef) ∧
  LinearMap.det (F : Herm →ₗ[ℝ] Herm) = 1

/-- **Section 8.** The intrinsic determinant-and-cone automorphism group of the Hermitian
carrier, defined using carrier data only. -/
def DetConeAut : Subgroup (Herm ≃ₗ[ℝ] Herm) where
  carrier := {F | IsDetConeAut F}
  one_mem' := by
    refine ⟨fun H => rfl, fun H => Iff.rfl, ?_⟩
    show LinearMap.det (LinearMap.id : Herm →ₗ[ℝ] Herm) = 1
    simp
  mul_mem' := by
    rintro F G ⟨hF1, hF2, hF3⟩ ⟨hG1, hG2, hG3⟩
    refine ⟨fun H => ?_, fun H => ?_, ?_⟩
    · show ((F (G H) : Herm) : M2).det = _
      rw [hF1, hG1]
    · exact (hG2 H).trans (hF2 (G H))
    · have : ((F * G : Herm ≃ₗ[ℝ] Herm) : Herm →ₗ[ℝ] Herm)
          = (F : Herm →ₗ[ℝ] Herm) ∘ₗ (G : Herm →ₗ[ℝ] Herm) := rfl
      rw [this, LinearMap.det_comp, hF3, hG3, one_mul]
  inv_mem' := by
    rintro F ⟨h1, h2, h3⟩
    refine ⟨fun H => ?_, fun H => ?_, ?_⟩
    · have := h1 (F⁻¹ H)
      rw [show (F (F⁻¹ H) : Herm) = H from by
        show (F * F⁻¹) H = H
        rw [mul_inv_cancel]; rfl] at this
      exact this.symm
    · have := h2 (F⁻¹ H)
      rw [show (F (F⁻¹ H) : Herm) = H from by
        show (F * F⁻¹) H = H
        rw [mul_inv_cancel]; rfl] at this
      exact this.symm
    · have hcomp : ((F : Herm →ₗ[ℝ] Herm) ∘ₗ ((F⁻¹ : Herm ≃ₗ[ℝ] Herm) : Herm →ₗ[ℝ] Herm))
          = (LinearMap.id : Herm →ₗ[ℝ] Herm) := by
        apply LinearMap.ext
        intro H
        show F (F⁻¹ H) = H
        show (F * F⁻¹) H = H
        rw [mul_inv_cancel]; rfl
      have := congrArg LinearMap.det hcomp
      rw [LinearMap.det_comp, h3, one_mul] at this
      simpa using this

theorem mem_detConeAut {F : Herm ≃ₗ[ℝ] Herm} : F ∈ DetConeAut ↔ IsDetConeAut F := Iff.rfl

/-! ### The characterization by `SO⁺(1,3)` -/

theorem matOf_isLorentz {F : Herm ≃ₗ[ℝ] Herm}
    (h : ∀ H : Herm, ((F H : Herm) : M2).det = ((H : Herm) : M2).det) : IsLorentz (matOf F) := by
  apply isLorentz_of_preserves_Q4
  intro v
  have h1 : ((hermCoordEquiv (matOf F *ᵥ v) : Herm) : M2).det = ((Q4 (matOf F *ᵥ v) : ℝ) : ℂ) :=
    det_coords _
  rw [hermCoordEquiv_matOf_mulVec] at h1
  rw [h (hermCoordEquiv v)] at h1
  rw [det_coords v] at h1
  exact_mod_cast h1.symm

theorem futureCone_mem_iff {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) (h00 : 0 < L 0 0)
    (v : Fin 4 → ℝ) : L *ᵥ v ∈ FutureCone ↔ v ∈ FutureCone := by
  constructor
  · intro h
    have himg := futureCone_image_eq hL h00
    have : v = (J4 * Lᵀ * J4) *ᵥ (L *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, hL.inv_left, Matrix.one_mulVec]
    rw [this]
    have hinv : IsLorentz (J4 * Lᵀ * J4) := hL.of_inv
    have hinv00 : (J4 * Lᵀ * J4) 0 0 = L 0 0 := by
      simp [Matrix.mul_apply, J4, Matrix.diagonal_apply, Matrix.transpose_apply]
    exact (orthochronous_iff_preserves_futureCone hinv).1 (by rw [hinv00]; exact h00) _ h
  · exact (orthochronous_iff_preserves_futureCone hL).1 h00 v

/-- **Section 8, key theorem.** A carrier automorphism belongs to the intrinsic group exactly
when its coordinate matrix is proper orthochronous Lorentz. -/
theorem mem_detConeAut_iff_isSO13Plus (F : Herm ≃ₗ[ℝ] Herm) :
    F ∈ DetConeAut ↔ IsSO13Plus (matOf F) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hL : IsLorentz (matOf F) := matOf_isLorentz h1
    refine ⟨hL, ?_, ?_⟩
    · rw [det_matOf, h3]
    · refine (orthochronous_iff_preserves_futureCone hL).2 ?_
      intro v hv
      have hpsd : ((hermCoordEquiv v : Herm) : M2).PosSemidef := (psdCone_eq_futureCone v).2 hv
      have : ((F (hermCoordEquiv v) : Herm) : M2).PosSemidef := (h2 _).1 hpsd
      rw [← hermCoordEquiv_matOf_mulVec] at this
      exact (psdCone_eq_futureCone _).1 this
  · rintro ⟨hL, hdet, h00⟩
    refine ⟨?_, ?_, ?_⟩
    · intro H
      have hv : hermCoordEquiv (matOf F *ᵥ coordsOf (H : M2)) = F H := by
        rw [hermCoordEquiv_matOf_mulVec]
        congr 1
        exact hermCoordEquiv.apply_symm_apply H
      have h1 : ((F H : Herm) : M2).det = ((Q4 (matOf F *ᵥ coordsOf (H : M2)) : ℝ) : ℂ) := by
        rw [← hv]; exact det_coords _
      rw [hL.preserves_Q4] at h1
      rw [h1, ← det_eq_Q4_coords]
    · intro H
      have hv : hermCoordEquiv (matOf F *ᵥ coordsOf (H : M2)) = F H := by
        rw [hermCoordEquiv_matOf_mulVec]
        congr 1
        exact hermCoordEquiv.apply_symm_apply H
      have hH : hermCoordEquiv (coordsOf (H : M2)) = H := hermCoordEquiv.apply_symm_apply H
      constructor
      · intro hp
        have : coordsOf (H : M2) ∈ FutureCone := by
          apply (psdCone_eq_futureCone _).1
          show ((hermCoordEquiv (coordsOf (H : M2)) : Herm) : M2).PosSemidef
          rw [hH]; exact hp
        have h2 := (futureCone_mem_iff hL h00 (coordsOf (H : M2))).2 this
        have := (psdCone_eq_futureCone _).2 h2
        show ((F H : Herm) : M2).PosSemidef
        rw [← hv]
        exact this
      · intro hp
        have : matOf F *ᵥ coordsOf (H : M2) ∈ FutureCone := by
          apply (psdCone_eq_futureCone _).1
          rw [hv]
          exact hp
        have h2 := (futureCone_mem_iff hL h00 (coordsOf (H : M2))).1 this
        have := (psdCone_eq_futureCone _).2 h2
        show ((H : Herm) : M2).PosSemidef
        rw [← hH]
        exact this
    · rw [← det_matOf]; exact hdet

/-! ### The isomorphism with `SO⁺(1,3)` -/

/-- The transport of carrier automorphisms into `GL(4, ℝ)`, as a group homomorphism. -/
def matHom : (Herm ≃ₗ[ℝ] Herm) →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun := matOf
  map_one' := matOf_one
  map_mul' := matOf_mul

def matGL : (Herm ≃ₗ[ℝ] Herm) →* GL (Fin 4) ℝ := matHom.toHomUnits

@[simp] theorem matGL_coe (F : Herm ≃ₗ[ℝ] Herm) :
    ((matGL F : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = matOf F := rfl

/-- The homomorphism `Aut⁺_{det,𝒫}(A_sa) → SO⁺(1,3)`. -/
def detConeAutHom : DetConeAut →* Mink4.SO13Plus :=
  MonoidHom.codRestrict (matGL.comp DetConeAut.subtype) Mink4.SO13Plus
    (fun F => (mem_detConeAut_iff_isSO13Plus (F : Herm ≃ₗ[ℝ] Herm)).1 F.2)

@[simp] theorem detConeAutHom_coe (F : DetConeAut) :
    (((detConeAutHom F : Mink4.SO13Plus) : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
      = matOf (F : Herm ≃ₗ[ℝ] Herm) := rfl

theorem detConeAutHom_injective : Function.Injective detConeAutHom := by
  intro F G h
  have h1 : matOf (F : Herm ≃ₗ[ℝ] Herm) = matOf (G : Herm ≃ₗ[ℝ] Herm) := by
    rw [← detConeAutHom_coe, ← detConeAutHom_coe, h]
  exact Subtype.ext (matOf_injective h1)

/-- The linear automorphism of `ℝ⁴` attached to a Lorentz matrix. -/
def lorentzLinEquiv {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofLinear (Matrix.toLin' L) (Matrix.toLin' (J4 * Lᵀ * J4))
    (by
      apply LinearMap.ext
      intro v
      show L *ᵥ ((J4 * Lᵀ * J4) *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hL.inv_right, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro v
      show (J4 * Lᵀ * J4) *ᵥ (L *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hL.inv_left, Matrix.one_mulVec])

@[simp] theorem lorentzLinEquiv_apply {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L)
    (v : Fin 4 → ℝ) : lorentzLinEquiv hL v = L *ᵥ v := rfl

/-- The carrier automorphism attached to a Lorentz matrix. -/
def autOfLorentz {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) : Herm ≃ₗ[ℝ] Herm :=
  hermCoordEquiv.symm.trans ((lorentzLinEquiv hL).trans hermCoordEquiv)

theorem matOf_autOfLorentz {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) :
    matOf (autOfLorentz hL) = L := by
  have h : (coordEquivOf (autOfLorentz hL) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
      = Matrix.toLin' L := by
    apply LinearMap.ext
    intro v
    show hermCoordEquiv.symm (autOfLorentz hL (hermCoordEquiv v)) = Matrix.toLin' L v
    simp [autOfLorentz]
  rw [matOf, h, LinearMap.toMatrix'_toLin']

theorem detConeAutHom_surjective : Function.Surjective detConeAutHom := by
  intro L
  have hL : IsSO13Plus (((L : Mink4.SO13Plus) : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := L.2
  have hmem : autOfLorentz hL.1 ∈ DetConeAut := by
    rw [mem_detConeAut_iff_isSO13Plus, matOf_autOfLorentz]
    exact hL
  refine ⟨⟨autOfLorentz hL.1, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show matOf (autOfLorentz hL.1) = (((L : Mink4.SO13Plus) : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
  rw [matOf_autOfLorentz]

/-- **Section 8, main theorem.** The intrinsic determinant-and-positive-cone orientation
preserving automorphism group of the Hermitian carrier *is* the proper orthochronous Lorentz
group. -/
def detConeAut_mulEquiv_SO13Plus : DetConeAut ≃* Mink4.SO13Plus :=
  MulEquiv.ofBijective detConeAutHom ⟨detConeAutHom_injective, detConeAutHom_surjective⟩

/-! ## Section 9 : the Task 5 effective congruence group is that intrinsic group -/

theorem congr_mem_detConeAut {A : GL2C} (hA : A ∈ DetPreservingCongruence) :
    congrHermEquivG A ∈ DetConeAut := by
  rw [mem_detConeAut_iff_isSO13Plus]
  have : matOf (congrHermEquivG A) = repG4 A := rfl
  rw [this]
  exact repG4_isSO13Plus ⟨A, hA⟩

/-- The direct map `[A] ↦ (H ↦ A H Aᴴ)` at the level of groups (before quotienting). -/
def congrToAut : DetPreservingCongruence →* DetConeAut where
  toFun A := ⟨congrHermEquivG (A : GL2C), congr_mem_detConeAut A.2⟩
  map_one' := by
    apply Subtype.ext
    exact LinearEquiv.ext congrHermEquivG_one
  map_mul' A B := by
    apply Subtype.ext
    exact LinearEquiv.ext (congrHermEquivG_mul (A : GL2C) (B : GL2C))

theorem congrToAut_ker : congrToAut.ker = scalarCircleG := by
  rw [← detPreserving_rep_kernel]
  ext A
  constructor
  · intro h
    rw [MonoidHom.mem_ker] at h
    rw [repGSO_mem_ker_iff]
    have h1 : congrHermEquivG (A : GL2C) = 1 := congrArg Subtype.val h
    have h2 : matOf (congrHermEquivG (A : GL2C)) = matOf 1 := by rw [h1]
    rw [matOf_one] at h2
    exact h2
  · intro h
    rw [repGSO_mem_ker_iff] at h
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply matOf_injective
    show matOf (congrHermEquivG (A : GL2C)) = matOf (1 : Herm ≃ₗ[ℝ] Herm)
    rw [matOf_one]
    exact h

theorem congrToAut_surjective : Function.Surjective congrToAut := by
  intro F
  have hF : IsSO13Plus (matOf (F : Herm ≃ₗ[ℝ] Herm)) :=
    (mem_detConeAut_iff_isSO13Plus _).1 F.2
  obtain ⟨B, hB⟩ := rep_surjective (matOf (F : Herm ≃ₗ[ℝ] Herm)) hF
  refine ⟨⟨SLtoGL B, SL_le_detPreserving ⟨B, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  apply matOf_injective
  show matOf (congrHermEquivG (SLtoGL B)) = _
  have : matOf (congrHermEquivG (SLtoGL B)) = repG4 (SLtoGL B) := rfl
  rw [this, repG4_SLtoGL, hB]

/-- **Section 9, main theorem.** The Task 5 effective congruence group is *directly*
isomorphic to the intrinsic carrier automorphism group, by the map induced by
`[A] ↦ (H ↦ A H Aᴴ)`. -/
def effectiveCongruence_mulEquiv_detConeAut : DetQuotient ≃* DetConeAut :=
  (QuotientGroup.quotientMulEquivOfEq congrToAut_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective congrToAut congrToAut_surjective)

end Carrier
