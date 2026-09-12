import RequestProject.Spine.Cohomology.Coboundary

/-!
# Task 5, WP4 : genuine singular mod-2 cohomology as a quotient

`Zⁿ(X;ℤ₂) = ker δⁿ`, `Bⁿ(X;ℤ₂) = im δⁿ⁻¹` (with `B⁰ = 0`), `Bⁿ ⊆ Zⁿ`, and

`Hⁿ(X;ℤ₂) = Zⁿ(X;ℤ₂) / Bⁿ(X;ℤ₂)`

as an actual `Submodule.Quotient` — a genuine quotient object, not an opaque carrier and not a
typeclass input.  The definition is degree-generic (`n : ℕ` arbitrary), so in particular it
covers `n = 0,1,2,3,4`.

## Contents

* `Mod2Cohomology.cocycles`, `Mod2Cohomology.coboundaries`;
* `Mod2Cohomology.coboundaries_le_cocycles` (`Bⁿ ⊆ Zⁿ`, a theorem, from `δ² = 0`);
* `Mod2Cohomology.Cohomology X n`, with its derived `AddCommGroup` and `Module (ZMod 2)`
  structures;
* `Mod2Cohomology.cocycleOf` / `Mod2Cohomology.mk` — building classes from explicit cochains;
* the membership criteria `mk_eq_mk_iff`, `mk_eq_zero_iff`, and surjectivity of `mk`.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite

universe u

variable {X : TopCat.{u}}

/-! ## Cocycles and coboundaries -/

/-- `Zⁿ(X;ℤ₂) = ker δⁿ`, the module of singular mod-2 **cocycles**. -/
def cocycles (X : TopCat.{u}) (n : ℕ) : Submodule (ZMod 2) (Cochain X n) :=
  LinearMap.ker (d X n)

theorem mem_cocycles_iff {n : ℕ} {f : Cochain X n} :
    f ∈ cocycles X n ↔ d X n f = 0 := Iff.rfl

/-- `Bⁿ(X;ℤ₂) = im δⁿ⁻¹`, the module of singular mod-2 **coboundaries**; in degree `0` there
is no `δ⁻¹`, so `B⁰ = 0`. -/
def coboundaries (X : TopCat.{u}) : (n : ℕ) → Submodule (ZMod 2) (Cochain X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d X n)

@[simp] theorem coboundaries_zero : coboundaries X 0 = ⊥ := rfl

@[simp] theorem coboundaries_succ (n : ℕ) :
    coboundaries X (n + 1) = LinearMap.range (d X n) := rfl

theorem mem_coboundaries_succ_iff {n : ℕ} {f : Cochain X (n + 1)} :
    f ∈ coboundaries X (n + 1) ↔ ∃ g : Cochain X n, d X n g = f := Iff.rfl

/-- **`Bⁿ ⊆ Zⁿ`**: every coboundary is a cocycle.  In degree `0` this is trivial; in positive
degree it is exactly the theorem `δ² = 0`. -/
theorem coboundaries_le_cocycles (n : ℕ) : coboundaries X n ≤ cocycles X n := by
  cases n with
  | zero => simp [coboundaries]
  | succ n =>
      rintro f ⟨g, rfl⟩
      exact d_d n g

/-! ## The quotient -/

/-- `Bⁿ` viewed inside `Zⁿ`, i.e. the submodule of the cocycles consisting of coboundaries.
This is the submodule one quotients by. -/
def coboundariesIn (X : TopCat.{u}) (n : ℕ) : Submodule (ZMod 2) (cocycles X n) :=
  Submodule.comap (cocycles X n).subtype (coboundaries X n)

/-- **Singular mod-2 cohomology** `Hⁿ(X;ℤ₂) = Zⁿ/Bⁿ`, a genuine quotient module. -/
def Cohomology (X : TopCat.{u}) (n : ℕ) : Type u :=
  (cocycles X n) ⧸ (coboundariesIn X n)

instance (X : TopCat.{u}) (n : ℕ) : AddCommGroup (Cohomology X n) :=
  inferInstanceAs (AddCommGroup ((cocycles X n) ⧸ (coboundariesIn X n)))

instance (X : TopCat.{u}) (n : ℕ) : Module (ZMod 2) (Cohomology X n) :=
  inferInstanceAs (Module (ZMod 2) ((cocycles X n) ⧸ (coboundariesIn X n)))

/-- The cohomology class of a cocycle. -/
def mk {n : ℕ} (z : cocycles X n) : Cohomology X n :=
  Submodule.Quotient.mk (p := coboundariesIn X n) z

/-- A cochain that is annihilated by `δ`, packaged as an element of `Zⁿ`. -/
def cocycleOf {n : ℕ} (f : Cochain X n) (hf : d X n f = 0) : cocycles X n := ⟨f, hf⟩

@[simp] theorem cocycleOf_coe {n : ℕ} (f : Cochain X n) (hf : d X n f = 0) :
    (cocycleOf f hf : Cochain X n) = f := rfl

/-- The class of a cochain with vanishing coboundary. -/
def classOf {n : ℕ} (f : Cochain X n) (hf : d X n f = 0) : Cohomology X n :=
  mk (cocycleOf f hf)

theorem mk_add {n : ℕ} (z w : cocycles X n) : mk (z + w) = mk z + mk w := rfl

theorem mk_smul {n : ℕ} (c : ZMod 2) (z : cocycles X n) : mk (c • z) = c • mk z := rfl

@[simp] theorem mk_zero {n : ℕ} : mk (0 : cocycles X n) = 0 := rfl

/-- Two cocycles have the same class iff they differ by a coboundary. -/
theorem mk_eq_mk_iff {n : ℕ} (z w : cocycles X n) :
    mk z = mk w ↔ ((z : Cochain X n) - (w : Cochain X n)) ∈ coboundaries X n := by
  rw [mk, mk, Submodule.Quotient.eq]
  exact Iff.rfl

/-- A class vanishes iff a (hence any) representing cocycle is a coboundary. -/
theorem mk_eq_zero_iff {n : ℕ} (z : cocycles X n) :
    mk z = 0 ↔ (z : Cochain X n) ∈ coboundaries X n := by
  rw [mk, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- Every cohomology class comes from a cocycle. -/
theorem mk_surjective {n : ℕ} : Function.Surjective (mk : cocycles X n → Cohomology X n) :=
  Submodule.Quotient.mk_surjective _

/-- In degree `0` there are no non-trivial coboundaries, so `H⁰` is the module of `0`-cocycles
modulo nothing; the quotient map is injective. -/
theorem mk_injective_zero : Function.Injective (mk : cocycles X 0 → Cohomology X 0) := by
  intro z w h
  have := (mk_eq_mk_iff z w).1 h
  rw [coboundaries_zero, Submodule.mem_bot, sub_eq_zero] at this
  exact Subtype.ext this

end Mod2Cohomology
