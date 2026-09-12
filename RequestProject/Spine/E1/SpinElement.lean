import Mathlib
import RequestProject.Spine.E1.LorentzClifford

/-!
# Spine / E1 : spin *elements* of the intrinsic Clifford algebra

This is the **predicate layer** of the intrinsic spin core: it isolates the condition that
singles out spin elements inside `Cl₃(ℝ)`, together with the twisted action they carry on
the Lorentz carrier.  The *bundled* spin group is a separate layer
(`RequestProject.Spine.E1.SpinGroup`), and the covering homomorphism a further one
(`RequestProject.Spine.E1.SpinCover`).

Everything is intrinsic to `Cl₃(ℝ)`: no `SL(2,ℂ)`, no matrix model, no representation
space, no Hermitian data.

Definitions (all canonical constructions from the intrinsic Clifford data):

* `SpinCore.cconj` — Clifford conjugation `involute ∘ reverse` on `Cl₃(ℝ)`;
* `SpinCore.IsSpinElem g` — the intrinsic unit condition `g · cconj g = cconj g · g = 1`;
* `SpinCore.spinAct g x = g · A(x) · reverse g` — the twisted action on the embedded carrier,
  where `A = SpinCore.spinToCl`.

Proved:

* `SpinCore.isSpinElem_one`, `SpinCore.isSpinElem_neg_one`, `SpinCore.isSpinElem_mul`,
  `SpinCore.isSpinElem_cconj` — the spin elements form a multiplicative set containing `±1`
  and closed under Clifford conjugation (which is the inverse, `SpinCore.cconj_cconj`);
* `SpinCore.spinAct_one`, `SpinCore.spinAct_neg_one` — `±1` act identically: the kernel of the
  action contains `{±1}`;
* `SpinCore.spinAct_mul` — the action is multiplicative;
* **`SpinCore.spinAct_norm`** — a spin element preserves the intrinsic quadratic form:
  `spinAct g x · cconj (spinAct g x) = N(x)`, the Clifford form of `N`-preservation
  (`SpinCore.spinToCl_norm` records `A(x) · cconj A(x) = N(x)`).

The further facts — that `spinAct g x` again lies in the embedded carrier, that the induced
map is onto the intrinsic Lorentz group and that its kernel is exactly `{±1}` — are proved
downstream in `Paravector`, `SpinDeterminant`, `DoubleCover`, `SpinCover` and `SpinKernel`.
The comparison with `SL(2,ℂ)` is downstream of all of them and is never used by them.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

open SpinCore

/-! ## Clifford conjugation -/

/-- Clifford conjugation on `Cl₃(ℝ)`: the grade involution composed with reversion. -/
def cconj (x : Cl3) : Cl3 := involute (reverse (Q := q3) x)

@[simp] theorem cconj_one : cconj (1 : Cl3) = 1 := by simp [cconj]

@[simp] theorem cconj_neg (x : Cl3) : cconj (-x) = -cconj x := by
  simp [cconj]

/-- Clifford conjugation is an anti-homomorphism. -/
theorem cconj_mul (x y : Cl3) : cconj (x * y) = cconj y * cconj x := by
  simp [cconj, reverse.map_mul, map_mul]

/-- Clifford conjugation is an involution. -/
theorem cconj_cconj (x : Cl3) : cconj (cconj x) = x := by
  simp only [cconj, reverse_involute, involute_involute, reverse_reverse]

theorem involute_spinToCl (x : LorentzCarrier) : involute (spinToCl x) = spinToClBar x := by
  simp [spinToCl, spinToClBar, map_add, sub_eq_add_neg]

/-- `A(x) · cconj A(x) = N(x)`: the Clifford expression of the intrinsic quadratic form. -/
theorem spinToCl_norm (x : LorentzCarrier) :
    spinToCl x * cconj (spinToCl x) = algebraMap ℝ Cl3 (NS x) := by
  rw [cconj, reverse_spinToCl, involute_spinToCl, spinToCl_mul_bar]

/-! ## Spin elements -/

/-- The intrinsic spin condition inside `Cl₃(ℝ)`. -/
def IsSpinElem (g : Cl3) : Prop := g * cconj g = 1 ∧ cconj g * g = 1

theorem isSpinElem_one : IsSpinElem 1 := by
  constructor <;> simp

theorem isSpinElem_neg_one : IsSpinElem (-1 : Cl3) := by
  constructor <;> simp

theorem isSpinElem_mul {g h : Cl3} (hg : IsSpinElem g) (hh : IsSpinElem h) :
    IsSpinElem (g * h) := by
  refine ⟨?_, ?_⟩
  · rw [cconj_mul, ← mul_assoc, mul_assoc g h, hh.1, mul_one, hg.1]
  · rw [cconj_mul, mul_assoc, ← mul_assoc (cconj g), hg.2, one_mul, hh.2]

/-- The spin condition is stable under Clifford conjugation, which supplies the inverse. -/
theorem isSpinElem_cconj {g : Cl3} (hg : IsSpinElem g) : IsSpinElem (cconj g) :=
  ⟨by rw [cconj_cconj]; exact hg.2, by rw [cconj_cconj]; exact hg.1⟩

/-- From the spin condition: `reverse g · involute g = 1`. -/
theorem reverse_mul_involute {g : Cl3} (hg : IsSpinElem g) :
    reverse (Q := q3) g * involute g = 1 := by
  have h := congrArg (involute (Q := q3)) hg.2
  rw [map_mul, map_one, cconj] at h
  rwa [involute_involute] at h

/-! ## The twisted action -/

/-- The twisted action of a Clifford element on the embedded carrier. -/
def spinAct (g : Cl3) (x : LorentzCarrier) : Cl3 := g * spinToCl x * reverse (Q := q3) g

@[simp] theorem spinAct_one (x : LorentzCarrier) : spinAct 1 x = spinToCl x := by
  simp [spinAct]

/-- `-1` acts exactly as `1`: the kernel of the action contains `{±1}`. -/
@[simp] theorem spinAct_neg_one (x : LorentzCarrier) : spinAct (-1) x = spinToCl x := by
  simp [spinAct]

theorem spinAct_mul (g h : Cl3) (x : LorentzCarrier) :
    spinAct (g * h) x = g * spinAct h x * reverse (Q := q3) g := by
  simp only [spinAct, reverse.map_mul]
  noncomm_ring

/-- **Phase V (main partial result).**  A spin element preserves the intrinsic quadratic
form of the carrier, in its Clifford formulation. -/
theorem spinAct_norm {g : Cl3} (hg : IsSpinElem g) (x : LorentzCarrier) :
    spinAct g x * cconj (spinAct g x) = algebraMap ℝ Cl3 (NS x) := by
  have hrev : reverse (Q := q3) (spinAct g x) = spinAct g x := by
    simp only [spinAct, reverse.map_mul, reverse_reverse, reverse_spinToCl]
    rw [mul_assoc]
  have hc : cconj (spinAct g x)
      = involute g * spinToClBar x * involute (reverse (Q := q3) g) := by
    rw [cconj, hrev]
    simp only [spinAct, map_mul, involute_spinToCl]
  rw [hc]
  have hkey : spinToCl x * (reverse (Q := q3) g * involute g) * spinToClBar x
      = algebraMap ℝ Cl3 (NS x) := by
    rw [reverse_mul_involute hg, mul_one, spinToCl_mul_bar]
  calc g * spinToCl x * reverse (Q := q3) g
        * (involute g * spinToClBar x * involute (reverse (Q := q3) g))
      = g * (spinToCl x * (reverse (Q := q3) g * involute g) * spinToClBar x)
          * involute (reverse (Q := q3) g) := by noncomm_ring
    _ = g * algebraMap ℝ Cl3 (NS x) * cconj g := by rw [hkey, cconj]
    _ = algebraMap ℝ Cl3 (NS x) * (g * cconj g) := by
          rw [← Algebra.commutes, mul_assoc]
    _ = algebraMap ℝ Cl3 (NS x) := by rw [hg.1, mul_one]

end SpinCore
