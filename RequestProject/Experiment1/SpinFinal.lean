import Mathlib
import RequestProject.Experiment1.V3Restriction

/-!
# The final theorem hierarchy

This file packages the `PSL(2, ℂ)` quotient and records the axiom dependencies of the central
theorems.  The subgroup `{±I}` is defined *independently* of the representation, and only then
proved to be the kernel; the target group `Mink4.SO13Plus` is defined in
`RequestProject.Spine.Foundation.MinkowskiMatrix` by intrinsic conditions.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-- The subgroup `{I, -I}` of `SL(2, ℂ)`, defined independently of the representation. -/
def negPM : Subgroup SL2C where
  carrier := {A | A = 1 ∨ A = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · left
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply]
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · right
      have h : (-1 : SL2C) * (-1 : SL2C) = 1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg]
      exact inv_eq_of_mul_eq_one_right h

theorem mem_negPM (A : SL2C) : A ∈ negPM ↔ A = 1 ∨ A = -1 := Iff.rfl

/-- **Section 15.** The independently defined subgroup `{±I}` *is* the kernel of the
representation. -/
theorem negPM_eq_ker : negPM = repSO.ker := by
  ext A
  rw [mem_negPM, repSO_ker]

instance negPM_normal : negPM.Normal := by
  rw [negPM_eq_ker]
  exact MonoidHom.normal_ker repSO

/-- **Section 18.** `PSL(2, ℂ) := SL(2, ℂ) / {±I}`. -/
abbrev PSL2C := SL2C ⧸ negPM

/-- **Section 18, final theorem.** `PSL(2, ℂ) ≃* SO⁺(1,3)`, a genuine group isomorphism onto
the independently defined proper orthochronous Lorentz group. -/
def psl2C_mulEquiv_SO13Plus : PSL2C ≃* Mink4.SO13Plus :=
  (QuotientGroup.quotientMulEquivOfEq negPM_eq_ker).trans quotient_mulEquiv_SO13Plus

/-- The strongest conclusion, in one statement: the congruence action of `SL(2, ℂ)` on the
Hermitian carrier induces a surjective homomorphism onto the independently defined
`SO⁺(1,3)` with kernel exactly `{±I}`, hence `SL(2, ℂ)/{±I} ≅ SO⁺(1,3)`. -/
theorem spin_lorentz_double_cover :
    Function.Surjective repSO ∧ (∀ A : SL2C, A ∈ repSO.ker ↔ A = 1 ∨ A = -1) ∧
      Nonempty (PSL2C ≃* Mink4.SO13Plus) :=
  ⟨repSO_surjective, repSO_ker, ⟨psl2C_mulEquiv_SO13Plus⟩⟩

end SpinLorentz

/-! ## Axiom audit of the central theorems -/

#print axioms Herm2.hermCoordEquiv
#print axioms Herm2.det_coords
#print axioms Herm2.pauliBasis
#print axioms Herm2.pauli_anticommute
#print axioms Herm2.sigma3_eq_PP_sub_PM
#print axioms SpinLorentz.congruence_preserves_hermitian
#print axioms SpinLorentz.congruence_preserves_det
#print axioms SpinLorentz.rep_preserves_minkowski
#print axioms SpinLorentz.rep_isSO13Plus
#print axioms SpinLorentz.rep_kernel
#print axioms SpinLorentz.rep_surjective
#print axioms SpinLorentz.quotient_mulEquiv_SO13Plus
#print axioms SpinLorentz.psl2C_mulEquiv_SO13Plus
#print axioms SpinLorentz.v3_diagonal_restriction
#print axioms SpinLorentz.spin_lorentz_double_cover
