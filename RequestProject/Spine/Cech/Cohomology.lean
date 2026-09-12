import RequestProject.Spine.Cech.Coboundary

/-!
# Task 6, WP4 : fixed-cover Čech cohomology `Ȟⁿ(𝓤;ℤ₂)` as a genuine quotient

`Žⁿ(U;ℤ₂) = ker δⁿ`, `B̌ⁿ(U;ℤ₂) = im δⁿ⁻¹` (with `B̌⁰ = 0`), the theorem `B̌ⁿ ⊆ Žⁿ` (which is
exactly `δ² = 0`), and

`Ȟⁿ(U;ℤ₂) = Žⁿ(U;ℤ₂) / B̌ⁿ(U;ℤ₂)`

as an actual `Submodule.Quotient` — a genuine quotient object, not an opaque carrier, not a
predicate wrapper, and not a typeclass input.  The construction is degree-generic, so `Ȟ¹` and
`Ȟ²` (the two degrees explicitly required) are instances of it, and it is completely
independent of the Spin layer: nothing in this file or its imports mentions a group, a lift, a
projection or a defect.
-/

namespace CechZ2

universe w t

variable {X : Type w} {ι : Type t} {U : ι → Set X}

/-! ## Cocycles and coboundaries -/

/-- `Žⁿ(U;ℤ₂) = ker δⁿ`, the module of Čech **cocycles**. -/
def cocycles (U : ι → Set X) (n : ℕ) : Submodule (ZMod 2) (Cochain U n) :=
  LinearMap.ker (d U n)

theorem mem_cocycles_iff {n : ℕ} {c : Cochain U n} :
    c ∈ cocycles U n ↔ d U n c = 0 := Iff.rfl

/-- `B̌ⁿ(U;ℤ₂) = im δⁿ⁻¹`, the module of Čech **coboundaries**; in degree `0` there is no
`δ⁻¹`, so `B̌⁰ = 0`. -/
def coboundaries (U : ι → Set X) : (n : ℕ) → Submodule (ZMod 2) (Cochain U n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d U n)

@[simp] theorem coboundaries_zero : coboundaries U 0 = ⊥ := rfl

@[simp] theorem coboundaries_succ (n : ℕ) :
    coboundaries U (n + 1) = LinearMap.range (d U n) := rfl

theorem mem_coboundaries_succ_iff {n : ℕ} {c : Cochain U (n + 1)} :
    c ∈ coboundaries U (n + 1) ↔ ∃ b : Cochain U n, d U n b = c := Iff.rfl

/-- **`B̌ⁿ ⊆ Žⁿ`**: every Čech coboundary is a Čech cocycle.  In degree `0` this is trivial;
in positive degree it is exactly the theorem `δ² = 0`. -/
theorem coboundaries_le_cocycles (n : ℕ) : coboundaries U n ≤ cocycles U n := by
  cases n with
  | zero => simp [coboundaries]
  | succ n =>
      rintro c ⟨b, rfl⟩
      exact d_d n b

/-! ## The quotient -/

/-- `B̌ⁿ` viewed inside `Žⁿ`: the submodule of the cocycles consisting of coboundaries. -/
def coboundariesIn (U : ι → Set X) (n : ℕ) : Submodule (ZMod 2) (cocycles U n) :=
  Submodule.comap (cocycles U n).subtype (coboundaries U n)

/-- **Fixed-cover Čech cohomology** `Ȟⁿ(U;ℤ₂) = Žⁿ/B̌ⁿ`, a genuine quotient module. -/
def Cohomology (U : ι → Set X) (n : ℕ) : Type t :=
  (cocycles U n) ⧸ (coboundariesIn U n)

instance (U : ι → Set X) (n : ℕ) : AddCommGroup (Cohomology U n) :=
  inferInstanceAs (AddCommGroup ((cocycles U n) ⧸ (coboundariesIn U n)))

instance (U : ι → Set X) (n : ℕ) : Module (ZMod 2) (Cohomology U n) :=
  inferInstanceAs (Module (ZMod 2) ((cocycles U n) ⧸ (coboundariesIn U n)))

/-- The Čech cohomology class of a cocycle. -/
def mk {n : ℕ} (z : cocycles U n) : Cohomology U n :=
  Submodule.Quotient.mk (p := coboundariesIn U n) z

/-- A cochain annihilated by `δ`, packaged as an element of `Žⁿ`. -/
def cocycleOf {n : ℕ} (c : Cochain U n) (hc : d U n c = 0) : cocycles U n := ⟨c, hc⟩

@[simp] theorem cocycleOf_coe {n : ℕ} (c : Cochain U n) (hc : d U n c = 0) :
    (cocycleOf c hc : Cochain U n) = c := rfl

/-- The class of a cochain with vanishing coboundary. -/
def classOf {n : ℕ} (c : Cochain U n) (hc : d U n c = 0) : Cohomology U n :=
  mk (cocycleOf c hc)

theorem mk_add {n : ℕ} (z w : cocycles U n) : mk (z + w) = mk z + mk w := rfl

@[simp] theorem mk_zero {n : ℕ} : mk (0 : cocycles U n) = 0 := rfl

/-- Two cocycles have the same class iff they differ by a coboundary. -/
theorem mk_eq_mk_iff {n : ℕ} (z w : cocycles U n) :
    mk z = mk w ↔ ((z : Cochain U n) - (w : Cochain U n)) ∈ coboundaries U n := by
  rw [mk, mk, Submodule.Quotient.eq]
  exact Iff.rfl

/-- A class vanishes iff a (hence any) representing cocycle is a coboundary. -/
theorem mk_eq_zero_iff {n : ℕ} (z : cocycles U n) :
    mk z = 0 ↔ (z : Cochain U n) ∈ coboundaries U n := by
  rw [mk, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- A degree-`(n+1)` class vanishes iff its representative is `δ` of some `n`-cochain. -/
theorem mk_eq_zero_iff_exists {n : ℕ} (z : cocycles U (n + 1)) :
    mk z = 0 ↔ ∃ b : Cochain U n, d U n b = (z : Cochain U (n + 1)) := by
  rw [mk_eq_zero_iff]
  exact Iff.rfl

/-- Every Čech cohomology class comes from a cocycle. -/
theorem mk_surjective {n : ℕ} : Function.Surjective (mk : cocycles U n → Cohomology U n) :=
  Submodule.Quotient.mk_surjective _

/-! ## The two required instantiations

`Ȟ¹(U;ℤ₂)` and `Ȟ²(U;ℤ₂)` are the degree-`1` and degree-`2` instances of the generic
construction; the degree-two carrier is manifestly independent of any Spin datum — its
definition mentions only `U` and `ZMod 2`. -/

/-- `Ȟ¹(𝓤;ℤ₂)`. -/
abbrev H1 (U : ι → Set X) : Type t := Cohomology U 1

/-- `Ȟ²(𝓤;ℤ₂)`. -/
abbrev H2 (U : ι → Set X) : Type t := Cohomology U 2

end CechZ2
