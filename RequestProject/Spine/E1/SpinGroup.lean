import Mathlib
import RequestProject.Spine.E1.SpinElement
import RequestProject.Spine.E1.CliffordMonomial

/-!
# Spine / E1 : the intrinsic **bundled** spin group

The predicate layer `RequestProject.Spine.E1.SpinElement` characterises the spin elements of
the intrinsic real Clifford algebra `Cl₃(ℝ)` by

`IsSpinElem g ↔ g · cconj g = cconj g · g = 1`.

This module bundles them into a genuine group:

* `SpinCore.SpinGroup : Subgroup Cl3ˣ` — the spin elements, as a subgroup of the units of
  `Cl₃(ℝ)` (the inverse of a spin element is its Clifford conjugate);
* `SpinCore.spinUnit hg : Cl3ˣ` — the unit attached to a spin element, and
  `SpinCore.mkSpin hg : SpinGroup` its bundled form;
* `SpinCore.negOneSpin : SpinGroup` — the nontrivial central element `-1`, together with
  `SpinCore.negOneSpin_ne_one`;
* `SpinCore.spinGroup_neg_one_central` — `-1` commutes with every element of `Cl₃(ℝ)`.

**Import firewall.**  `Mathlib` plus the intrinsic Clifford / spin-element layer.  No
`SL(2,ℂ)`, no complex matrix model, no Hermitian data, no historical experiment module.

**Provenance.**  `SpinGroup` and `spinUnit` are the declarations `SpinCore.SpinGrp` and
`SpinCore.spinUnit` of `RequestProject.Spine.E1.SL2Comparison`, moved here unchanged apart
from the name of the subgroup (`SpinGrp → SpinGroup`, per the naming discipline of this
refactor).  Upstream they were introduced in the historical experiment-1 module
`Task11SpinSL2` / `SpinFinal`.  Nothing is strengthened.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-- The intrinsic **spin group**: the units of `Cl₃(ℝ)` satisfying the intrinsic spin
condition `g · cconj g = cconj g · g = 1`. -/
def SpinGroup : Subgroup Cl3ˣ where
  carrier := {u | IsSpinElem (u : Cl3)}
  mul_mem' ha hb := isSpinElem_mul ha hb
  one_mem' := isSpinElem_one
  inv_mem' := by
    intro u hu
    have hinv : ((u⁻¹ : Cl3ˣ) : Cl3) = cconj (u : Cl3) :=
      Units.inv_eq_of_mul_eq_one_right hu.1
    rw [Set.mem_setOf_eq, hinv]
    exact isSpinElem_cconj hu

@[simp] theorem mem_SpinGroup {u : Cl3ˣ} : u ∈ SpinGroup ↔ IsSpinElem (u : Cl3) := Iff.rfl

/-- The unit of `Cl₃(ℝ)` attached to a spin element, with inverse its Clifford conjugate. -/
def spinUnit {g : Cl3} (hg : IsSpinElem g) : Cl3ˣ := ⟨g, cconj g, hg.1, hg.2⟩

@[simp] theorem spinUnit_coe {g : Cl3} (hg : IsSpinElem g) : ((spinUnit hg : Cl3ˣ) : Cl3) = g :=
  rfl

theorem spinUnit_mem {g : Cl3} (hg : IsSpinElem g) : spinUnit hg ∈ SpinGroup := hg

/-- The bundled element of the spin group attached to a spin element. -/
def mkSpin {g : Cl3} (hg : IsSpinElem g) : SpinGroup := ⟨spinUnit hg, spinUnit_mem hg⟩

@[simp] theorem mkSpin_coe {g : Cl3} (hg : IsSpinElem g) :
    (((mkSpin hg : SpinGroup) : Cl3ˣ) : Cl3) = g := rfl

/-- Every element of the spin group is of this shape. -/
theorem exists_mkSpin (u : SpinGroup) : ∃ (g : Cl3) (hg : IsSpinElem g), mkSpin hg = u := by
  refine ⟨((u : Cl3ˣ) : Cl3), u.2, ?_⟩
  exact Subtype.ext (Units.ext rfl)

/-! ## The element `-1` -/

theorem neg_one_mem_SpinGroup : (-1 : Cl3ˣ) ∈ SpinGroup := by
  have : ((-1 : Cl3ˣ) : Cl3) = -1 := by simp
  rw [mem_SpinGroup, this]
  exact isSpinElem_neg_one

/-- The nontrivial element `-1` of the intrinsic spin group. -/
def negOneSpin : SpinGroup := ⟨-1, neg_one_mem_SpinGroup⟩

@[simp] theorem negOneSpin_coe : (((negOneSpin : SpinGroup) : Cl3ˣ) : Cl3) = -1 := by
  simp [negOneSpin]

/-- `1 ≠ -1` in `Cl₃(ℝ)`: the algebra is not of characteristic two, so the spin group really
does have a nontrivial `{±1}`. -/
theorem one_ne_neg_one_Cl3 : (1 : Cl3) ≠ -1 := by
  intro h
  have h2 : (2 : ℝ) • (1 : Cl3) + (0 : ℝ) • omega = 0 := by
    rw [zero_smul, add_zero, two_smul]
    nth_rewrite 2 [h]
    simp
  have := (one_omega_indep h2).1
  norm_num at this

@[simp] theorem negOneSpin_sq : negOneSpin ^ 2 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, negOneSpin_coe]
  simp

theorem negOneSpin_ne_one : negOneSpin ≠ 1 := by
  intro h
  have := congrArg (fun u : SpinGroup => ((u : Cl3ˣ) : Cl3)) h
  simp only [negOneSpin_coe] at this
  exact one_ne_neg_one_Cl3 (by simpa using this.symm)

/-- `-1` is central in `Cl₃(ℝ)`, hence in the spin group. -/
theorem spinGroup_neg_one_central (u : SpinGroup) : negOneSpin * u = u * negOneSpin := by
  refine Subtype.ext (Units.ext ?_)
  show ((negOneSpin : Cl3ˣ) : Cl3) * ((u : Cl3ˣ) : Cl3)
      = ((u : Cl3ˣ) : Cl3) * ((negOneSpin : Cl3ˣ) : Cl3)
  simp [negOneSpin_coe]

end SpinCore
