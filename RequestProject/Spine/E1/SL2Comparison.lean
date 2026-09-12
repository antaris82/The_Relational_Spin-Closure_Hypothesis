import Mathlib
import RequestProject.Spine.E1.SpinKernel
import RequestProject.Spine.E1.PauliRepresentation

/-!
# Spine / E1 : the `SL(2,ℂ)` **comparison** layer

This module is a *downstream comparison* of the intrinsic spin core, not a part of it.  The
intrinsic objects

* `SpinCore.SpinGroup : Subgroup Cl3ˣ` (`RequestProject.Spine.E1.SpinGroup`),
* `SpinCore.spinCover : SpinGroup →* GLor` (`RequestProject.Spine.E1.SpinCover`),
* surjectivity of `spinCover` and its exact `{±1}` kernel
  (`RequestProject.Spine.E1.SpinCover`, `RequestProject.Spine.E1.SpinKernel`)

are all defined and proved *before* this module and without any of its content.  Here we add
only the identification of the intrinsic spin group with the matrix group `SL(2,ℂ)`, and the
compatibility of the two descriptions.

Content:

* `SpinCore.rho_cconj` — under the Pauli representation `rho`, Clifford conjugation becomes
  the 2×2 adjugate `trace (rho g) • 1 - rho g`;
* `SpinCore.mul_cconj_matrix` / `SpinCore.cconj_mul_matrix` — the 2×2 Cayley–Hamilton
  identity;
* **`SpinCore.isSpinElem_iff_det`** — `IsSpinElem g ↔ det (rho g) = 1`;
* **`SpinCore.spinEquivSL2 : SpinGroup ≃* SL(2,ℂ)`** — the comparison isomorphism, with
  `SpinCore.spinEquivSL2_coe` recording that it is implemented by `rho`;
* `SpinCore.spinEquivSL2_negOne` — the intrinsic kernel element `-1` corresponds to `-I₂`;
* **`SpinCore.sl2_comparison`** — the bundled comparison statement: the intrinsic spin group
  is isomorphic to `SL(2,ℂ)` *and* the intrinsic double cover
  (surjectivity + exact `{±1}` kernel) holds, the latter quoted from the intrinsic layer.

The proof of the comparison is necessarily model-assisted: the target `SL(2,ℂ)` is a matrix
group, so the faithful representation `SpinCore.rho : Cl₃(ℝ) →ₐ[ℝ] M₂(ℂ)` of
`RequestProject.Spine.E1.PauliRepresentation` is used.  That import lives *here* and is not
visible from the intrinsic core.

Nothing physical is claimed: `SL(2,ℂ)` is the group of complex 2×2 matrices of determinant
one, and `G_L` is the intrinsic Lorentz group of the carrier.

**Provenance.**  The declarations `SpinCore.SpinGrp`, `SpinCore.spinUnit`,
`SpinCore.spinCover`, `SpinCore.spinCover_apply`, `SpinCore.spinCover_surjective` and
`SpinCore.spinCover_kernel` used to live in this module; they were moved to
`RequestProject.Spine.E1.SpinGroup`, `.SpinCover` and `.SpinKernel` (see
`REFACTOR_AUDIT.md`).  The material that remains is unchanged, except that it now refers to
the moved names, and that the old bundled endpoint `SpinCore.task11_V5` is restated as
`SpinCore.sl2_comparison`.
-/

noncomputable section

open CliffordAlgebra Complex

namespace SpinCore

/-! ## Clifford conjugation in the Pauli model -/

theorem cconj_add (x y : Cl3) : cconj (x + y) = cconj x + cconj y := by
  simp [cconj]

theorem cconj_smul (a : ℝ) (x : Cl3) : cconj (a • x) = a • cconj x := by
  simp [cconj]

theorem cconj_cle (i : Fin 3) : cconj (cle i) = - cle i := by
  simp [cconj, cle]

theorem cconj_omega : cconj omega = omega := by
  rw [omega, cconj_mul, cconj_mul, cconj_cle, cconj_cle, cconj_cle]
  simp only [mul_assoc, s20, t10, t21, mul_neg, neg_neg, neg_mul]

theorem cconj_cle_pair {i j : Fin 3} (h : i ≠ j) : cconj (cle i * cle j) = -(cle i * cle j) := by
  rw [cconj_mul, cconj_cle, cconj_cle]
  simp only [neg_mul, mul_neg, neg_neg]
  rw [cle_anticomm h, neg_neg]

/-- Clifford conjugation in monomial coordinates: it fixes the grade-0 and grade-3 parts and
negates the grade-1 and grade-2 parts. -/
theorem cconj_monoComb (c : Fin 8 → ℝ) :
    cconj (monoComb c) = monoComb ![c 0, -c 1, -c 2, -c 3, -c 4, -c 5, -c 6, c 7] := by
  rw [monoComb_expand, monoComb_expand]
  simp only [cconj_add, cconj_smul, cconj_one, cconj_cle, cconj_omega,
    cconj_cle_pair (i := 0) (j := 1) (by decide),
    cconj_cle_pair (i := 0) (j := 2) (by decide),
    cconj_cle_pair (i := 1) (j := 2) (by decide),
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [smul_neg, neg_smul]

/-- Under the Pauli representation, Clifford conjugation is the 2×2 adjugate. -/
theorem rho_cconj (g : Cl3) : rho (cconj g) = (Matrix.trace (rho g)) • (1 : M2) - rho g := by
  obtain ⟨c, rfl⟩ := exists_monoComb g
  rw [cconj_monoComb, rho_monoComb, rho_monoComb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Complex.ext_iff] <;> try ring
  all_goals exact ⟨trivial, trivial⟩

/-! ## The 2×2 Cayley–Hamilton identity -/

theorem mul_cconj_matrix (M : M2) : M * (Matrix.trace M • (1 : M2) - M) = M.det • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

theorem cconj_mul_matrix (M : M2) : (Matrix.trace M • (1 : M2) - M) * M = M.det • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

/-- **Key step.**  The intrinsic spin condition is exactly unit determinant in the Pauli
model. -/
theorem isSpinElem_iff_det (g : Cl3) : IsSpinElem g ↔ (rho g).det = 1 := by
  constructor
  · rintro ⟨h1, -⟩
    have hr := congrArg rho h1
    rw [map_mul, rho_cconj, mul_cconj_matrix, map_one] at hr
    have h00 := congrArg (fun M : M2 => M 0 0) hr
    simpa [Matrix.one_apply] using h00
  · intro hdet
    refine ⟨?_, ?_⟩
    · exact rho_injective (by rw [map_mul, rho_cconj, mul_cconj_matrix, hdet, map_one, one_smul])
    · exact rho_injective (by rw [map_mul, rho_cconj, cconj_mul_matrix, hdet, map_one, one_smul])

/-! ## The comparison isomorphism `SpinGroup ≃* SL(2,ℂ)` -/

/-- The Pauli representation, restricted to the intrinsic spin group, lands in `SL(2,ℂ)`. -/
def spinToSL2 : SpinGroup →* Matrix.SpecialLinearGroup (Fin 2) ℂ where
  toFun u := ⟨rho ((u : Cl3ˣ) : Cl3), (isSpinElem_iff_det _).1 u.2⟩
  map_one' := by ext i j; simp
  map_mul' a b := by ext i j; simp [map_mul]

@[simp] theorem spinToSL2_coe (u : SpinGroup) :
    ((spinToSL2 u : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = rho ((u : Cl3ˣ) : Cl3) := rfl

theorem spinToSL2_injective : Function.Injective spinToSL2 := by
  intro u v h
  have hr : rho ((u : Cl3ˣ) : Cl3) = rho ((v : Cl3ˣ) : Cl3) := congrArg Subtype.val h
  exact Subtype.ext (Units.ext (rho_injective hr))

theorem spinToSL2_surjective : Function.Surjective spinToSL2 := by
  intro A
  set g : Cl3 := cliffordEquivM2.symm (A : Matrix (Fin 2) (Fin 2) ℂ) with hgdef
  have hrho : rho g = (A : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hgdef, ← cliffordEquivM2_apply, AlgEquiv.apply_symm_apply]
  have hg : IsSpinElem g := (isSpinElem_iff_det g).2 (by rw [hrho]; exact A.2)
  refine ⟨mkSpin hg, ?_⟩
  ext i j
  simp [spinToSL2, hrho]

/-- **Comparison.**  The intrinsic spin group of `Cl₃(ℝ)` is isomorphic, as a group, to
`SL(2,ℂ)`. -/
def spinEquivSL2 : SpinGroup ≃* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective spinToSL2 ⟨spinToSL2_injective, spinToSL2_surjective⟩

@[simp] theorem spinEquivSL2_coe (u : SpinGroup) :
    ((spinEquivSL2 u : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = rho ((u : Cl3ˣ) : Cl3) := rfl

/-- **Compatibility of the two descriptions of the kernel.**  The intrinsic kernel element
`-1` of the spin group corresponds to `-I₂ ∈ SL(2,ℂ)`. -/
theorem spinEquivSL2_negOne :
    ((spinEquivSL2 negOneSpin : Matrix.SpecialLinearGroup (Fin 2) ℂ)
      : Matrix (Fin 2) (Fin 2) ℂ) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [spinEquivSL2_coe, negOneSpin_coe, map_neg, map_one]

/-! ## The bundled comparison statement -/

/-- **The `SL(2,ℂ)` realization.**

The intrinsic spin group `SpinGroup = {g ∈ Cl₃(ℝ) : g cconj g = cconj g g = 1}` is
isomorphic to `SL(2,ℂ)`, and — quoted here from the intrinsic layer, which does not use the
comparison — its action on the carrier is a surjection onto the intrinsic Lorentz group
`G_L` whose kernel is exactly the central `{±1}`. -/
theorem sl2_comparison :
    Nonempty (SpinGroup ≃* Matrix.SpecialLinearGroup (Fin 2) ℂ) ∧
    Function.Surjective spinCover ∧
    (∀ u : SpinGroup, u ∈ spinCover.ker ↔ u = 1 ∨ u = negOneSpin) :=
  ⟨⟨spinEquivSL2⟩, spinCover_surjective, mem_ker_spinCover_iff⟩

end SpinCore

/-! ## Axiom audit of the comparison endpoint -/

-- Must report only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms SpinCore.spinEquivSL2
#print axioms SpinCore.sl2_comparison
