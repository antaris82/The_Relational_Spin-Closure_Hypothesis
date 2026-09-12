import Mathlib
import RequestProject.Experiment1.SpinLifts

/-!
# Surjectivity of the representation and the quotient isomorphism

The representation `SpinLorentz.rep : SL(2, ℂ) → M₄(ℝ)` is shown to be *onto* the
independently defined proper orthochronous Lorentz group `Mink4.SO13Plus` (which is defined in
`RequestProject.Spine.Foundation.MinkowskiMatrix` by the intrinsic conditions `LᵀJL = J`, `det L = 1`, `L 0 0 > 0`,
never as the image of `rep`).  Combined with `SpinLorentz.repSO_ker` this yields the group
isomorphism `SL(2, ℂ) / {±I} ≃* SO⁺(1,3)`.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-! ## Section 16 : surjectivity -/

/-- **Section 16.** Every element of the independently defined `SO⁺(1,3)` is `rep A` for some
`A ∈ SL(2, ℂ)`.

The proof is the standard structural one: `A_B` is the explicit pure boost carrying `e₀` to the
future unit timelike vector `L e₀`; then `rep A_B⁻¹ * L` fixes `e₀`, hence is a spatial rotation
`rotMat R` with `R ∈ SO(3)`, which is lifted through the Euler decomposition
`R = Rz(α) Ry(β) Rz(γ)` by the corresponding `SU(2)` elements. -/
theorem rep_surjective (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsSO13Plus L) :
    ∃ A : SL2C, rep A = L := by
  set w : Fin 4 → ℝ := fun i => L i 0 with hw
  have hQ : Q4 w = 1 := by
    have := hL.1.col_zero_rel
    simp only [Q4, hw]
    linarith
  have hw0 : 0 < w 0 := hL.2.2
  set AB := boostToSL hQ hw0 with hAB
  have hcol : ∀ i, rep AB i 0 = L i 0 := fun i => rep_boostTo_col_zero hQ hw0 i
  set L' := rep AB⁻¹ * L with hL'
  have hinv : rep AB⁻¹ * rep AB = 1 := by rw [← rep_mul]; simp [rep_one]
  have hfix : ∀ i, L' i 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) i 0 := by
    intro i
    have hstep : L' i 0 = (rep AB⁻¹ * rep AB) i 0 := by
      simp only [hL', Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => by rw [hcol k])
    rw [hstep, hinv]
  have hL'so : IsSO13Plus L' := (rep_isSO13Plus AB⁻¹).mul hL
  obtain ⟨R, hR, hLR⟩ := exists_rot_of_fixes_e0 hL'so
    (by simpa [Matrix.one_apply] using hfix 0) (by simpa [Matrix.one_apply] using hfix 1)
    (by simpa [Matrix.one_apply] using hfix 2) (by simpa [Matrix.one_apply] using hfix 3)
  obtain ⟨α, β, γ, hEuler⟩ := exists_euler hR
  refine ⟨AB * (rotZLift α * rotYLift β * rotZLift γ), ?_⟩
  rw [rep_mul, rep_mul, rep_mul, rep_rotZLift, rep_rotYLift, rep_rotZLift,
    ← rotMat_mul, ← rotMat_mul, ← hEuler, ← hLR, hL', ← Matrix.mul_assoc]
  rw [show rep AB * rep AB⁻¹ = 1 by rw [← rep_mul]; simp [rep_one], Matrix.one_mul]

/-- **Section 16.** Surjectivity of the group homomorphism into `SO⁺(1,3)`. -/
theorem repSO_surjective : Function.Surjective repSO := by
  intro g
  obtain ⟨A, hA⟩ := rep_surjective ((g : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) g.2
  exact ⟨A, Subtype.ext (Units.ext hA)⟩

/-! ## Section 18 : the quotient -/

/-- **Section 18.** `SL(2, ℂ)/ker ≃* SO⁺(1,3)`, with the kernel identified as `{±I}` in
`repSO_ker`. -/
def quotient_mulEquiv_SO13Plus : SL2C ⧸ repSO.ker ≃* Mink4.SO13Plus :=
  QuotientGroup.quotientKerEquivOfSurjective repSO repSO_surjective

/-- The kernel subgroup, explicitly `{I, -I}`. -/
theorem repSO_ker_eq : (repSO.ker : Set SL2C) = {1, -1} := by
  ext A
  simpa using repSO_ker A

end SpinLorentz
