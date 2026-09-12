import RequestProject.Spine.Cohomology.Cup
import RequestProject.Spine.Cohomology.Functorial

/-!
# Task 5, WP6 (part 3) : descent of the cup product to cohomology

From the Leibniz rule (`Mod2Cohomology.coboundary_cup`) we derive

* `cup_cocycle` : the cup product of two cocycles is a cocycle (any degrees);
* the four *absorption* lemmas in the degrees needed here, saying that changing one factor by
  a coboundary changes the product by a coboundary;

and then construct the two bilinear cup products on cohomology required by Task 5,

`cupH11 : H¹ × H¹ → H²`  and  `cupH22 : H² × H² → H⁴`,

together with the two cup squares `x ↦ x ⌣ x`.  Both are honest `ZMod 2`-bilinear maps of the
genuine quotient modules, obtained by `Submodule.liftQ` in each variable.

No Steenrod machinery is constructed here: `cupSquare1` and `cupSquare2` are the *cup squares*
`x ↦ x ⌣ x`, which is all that the Wu-class route of a future task needs in these degrees.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite SimplexCategory

universe u

variable {X : TopCat.{u}}

/-! ## The cup product of cocycles is a cocycle -/

/-- The cup product of two cocycles is a cocycle: both terms of the Leibniz rule vanish. -/
theorem cup_cocycle {p q : ℕ} {f : Cochain X p} {g : Cochain X q}
    (hf : d X p f = 0) (hg : d X q g = 0) : d X (p + q) (cup f g) = 0 := by
  funext τ
  have h := coboundary_cup f g τ
  have hf' : coboundary p f (reindex (frontBig p q) τ) = 0 := congrFun hf _
  have hg' : coboundary q g (reindex (backIncl p (q + 1)) τ) = 0 := congrFun hg _
  simp only [d_apply] at *
  rw [h, hf', hg']
  simp

/-- The cup product of two cocycles, as a cocycle. -/
def cupCocycle {p q : ℕ} (z : cocycles X p) (w : cocycles X q) : cocycles X (p + q) :=
  ⟨cup (z : Cochain X p) (w : Cochain X q), cup_cocycle z.2 w.2⟩

@[simp] theorem cupCocycle_coe {p q : ℕ} (z : cocycles X p) (w : cocycles X q) :
    ((cupCocycle z w : cocycles X (p + q)) : Cochain X (p + q))
      = cup (z : Cochain X p) (w : Cochain X q) := rfl

/-! ## Absorption of coboundaries, in the degrees `(1,1)` and `(2,2)`

In each case the required identification of two of the Alexander–Whitney inclusions holds
definitionally, because the degrees are numerals. -/

theorem cup_delta_left_11 (a : Cochain X 0) {g : Cochain X 1} (hg : d X 1 g = 0) :
    cup (d X 0 a) g = d X 1 (cup a g) := by
  funext τ
  have h := coboundary_cup (p := 0) (q := 1) a g τ
  have hg' : coboundary 1 g (reindex (backIncl 0 2) τ) = 0 := congrFun hg _
  simp only [d_apply, cup_apply] at *
  rw [h, hg']
  simp only [mul_zero, add_zero]
  rfl

theorem cup_delta_right_11 {f : Cochain X 1} (hf : d X 1 f = 0) (b : Cochain X 0) :
    cup f (d X 0 b) = d X 1 (cup f b) := by
  funext τ
  have h := coboundary_cup (p := 1) (q := 0) f b τ
  have hf' : coboundary 1 f (reindex (frontBig 1 0) τ) = 0 := congrFun hf _
  simp only [d_apply, cup_apply] at *
  rw [h, hf']
  simp only [zero_mul, zero_add]

theorem cup_delta_left_22 (a : Cochain X 1) {g : Cochain X 2} (hg : d X 2 g = 0) :
    cup (d X 1 a) g = d X 3 (cup a g) := by
  funext τ
  have h := coboundary_cup (p := 1) (q := 2) a g τ
  have hg' : coboundary 2 g (reindex (backIncl 1 3) τ) = 0 := congrFun hg _
  simp only [d_apply, cup_apply] at *
  rw [h, hg']
  simp only [mul_zero, add_zero]
  rfl

theorem cup_delta_right_22 {f : Cochain X 2} (hf : d X 2 f = 0) (b : Cochain X 1) :
    cup f (d X 1 b) = d X 3 (cup f b) := by
  funext τ
  have h := coboundary_cup (p := 2) (q := 1) f b τ
  have hf' : coboundary 2 f (reindex (frontBig 2 1) τ) = 0 := congrFun hf _
  simp only [d_apply, cup_apply] at *
  rw [h, hf']
  simp only [zero_mul, zero_add]

/-! ## `H¹ × H¹ → H²` -/

/-- For a fixed `1`-cocycle `z`, cupping on the left, as a linear map into `H²`. -/
def cupRight11Aux (z : cocycles X 1) : cocycles X 1 →ₗ[ZMod 2] Cohomology X 2 where
  toFun w := mk (cupCocycle z w)
  map_add' w₁ w₂ := by
    show mk (cupCocycle z (w₁ + w₂)) = mk (cupCocycle z w₁) + mk (cupCocycle z w₂)
    rw [← mk_add]
    exact congrArg mk (Subtype.ext (cup_add_right _ _ _))
  map_smul' c w := by
    show mk (cupCocycle z (c • w)) = c • mk (cupCocycle z w)
    rw [← mk_smul]
    exact congrArg mk (Subtype.ext (cup_smul_right _ _ _))

/-- Cupping with a fixed `1`-cocycle descends to `H¹ → H²`. -/
def cupRight11 (z : cocycles X 1) : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 2 :=
  Submodule.liftQ _ (cupRight11Aux z) (by
    rintro ⟨w, hw⟩ hmem
    obtain ⟨b, hb⟩ : ∃ b : Cochain X 0, d X 0 b = w := hmem
    show mk (cupCocycle z ⟨w, hw⟩) = 0
    rw [mk_eq_zero_iff]
    refine ⟨cup (z : Cochain X 1) b, ?_⟩
    rw [← cup_delta_right_11 z.2 b, hb]
    rfl)

@[simp] theorem cupRight11_mk (z w : cocycles X 1) :
    cupRight11 z (mk w) = mk (cupCocycle z w) := rfl

/-- The cup product `H¹ × H¹ → H²`, linear in the first variable before descent. -/
def cupH11Aux : cocycles X 1 →ₗ[ZMod 2] Cohomology X 1 →ₗ[ZMod 2] Cohomology X 2 where
  toFun := cupRight11
  map_add' z₁ z₂ := by
    ext x
    obtain ⟨w, rfl⟩ := mk_surjective x
    show mk (cupCocycle (z₁ + z₂) w) = mk (cupCocycle z₁ w) + mk (cupCocycle z₂ w)
    rw [← mk_add]
    exact congrArg mk (Subtype.ext (cup_add_left _ _ _))
  map_smul' c z := by
    ext x
    obtain ⟨w, rfl⟩ := mk_surjective x
    show mk (cupCocycle (c • z) w) = c • mk (cupCocycle z w)
    rw [← mk_smul]
    exact congrArg mk (Subtype.ext (cup_smul_left _ _ _))

/-- **The cup product `H¹(X;ℤ₂) × H¹(X;ℤ₂) → H²(X;ℤ₂)`**. -/
def cupH11 : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 1 →ₗ[ZMod 2] Cohomology X 2 :=
  Submodule.liftQ _ cupH11Aux (by
    rintro ⟨z, hz⟩ hmem
    obtain ⟨a, ha⟩ : ∃ a : Cochain X 0, d X 0 a = z := hmem
    ext x
    obtain ⟨w, rfl⟩ := mk_surjective x
    show mk (cupCocycle ⟨z, hz⟩ w) = 0
    rw [mk_eq_zero_iff]
    refine ⟨cup a (w : Cochain X 1), ?_⟩
    rw [← cup_delta_left_11 a w.2, ha]
    rfl)

@[simp] theorem cupH11_mk_mk (z w : cocycles X 1) :
    cupH11 (mk z) (mk w) = mk (cupCocycle z w) := rfl

/-- The cup square `H¹ → H²`, `x ↦ x ⌣ x`. -/
def cupSquare1 (x : Cohomology X 1) : Cohomology X 2 := cupH11 x x

@[simp] theorem cupSquare1_mk (z : cocycles X 1) :
    cupSquare1 (mk z) = mk (cupCocycle z z) := rfl

/-! ## `H² × H² → H⁴` -/

/-- For a fixed `2`-cocycle `z`, cupping on the left, as a linear map into `H⁴`. -/
def cupRight22Aux (z : cocycles X 2) : cocycles X 2 →ₗ[ZMod 2] Cohomology X 4 where
  toFun w := mk (cupCocycle z w)
  map_add' w₁ w₂ := by
    show mk (cupCocycle z (w₁ + w₂)) = mk (cupCocycle z w₁) + mk (cupCocycle z w₂)
    rw [← mk_add]
    exact congrArg mk (Subtype.ext (cup_add_right _ _ _))
  map_smul' c w := by
    show mk (cupCocycle z (c • w)) = c • mk (cupCocycle z w)
    rw [← mk_smul]
    exact congrArg mk (Subtype.ext (cup_smul_right _ _ _))

/-- Cupping with a fixed `2`-cocycle descends to `H² → H⁴`. -/
def cupRight22 (z : cocycles X 2) : Cohomology X 2 →ₗ[ZMod 2] Cohomology X 4 :=
  Submodule.liftQ _ (cupRight22Aux z) (by
    rintro ⟨w, hw⟩ hmem
    obtain ⟨b, hb⟩ : ∃ b : Cochain X 1, d X 1 b = w := hmem
    show mk (cupCocycle z ⟨w, hw⟩) = 0
    rw [mk_eq_zero_iff]
    refine ⟨cup (z : Cochain X 2) b, ?_⟩
    rw [← cup_delta_right_22 z.2 b, hb]
    rfl)

/-- The cup product `H² × H² → H⁴`, linear in the first variable before descent. -/
def cupH22Aux : cocycles X 2 →ₗ[ZMod 2] Cohomology X 2 →ₗ[ZMod 2] Cohomology X 4 where
  toFun := cupRight22
  map_add' z₁ z₂ := by
    ext x
    obtain ⟨w, rfl⟩ := mk_surjective x
    show mk (cupCocycle (z₁ + z₂) w) = mk (cupCocycle z₁ w) + mk (cupCocycle z₂ w)
    rw [← mk_add]
    exact congrArg mk (Subtype.ext (cup_add_left _ _ _))
  map_smul' c z := by
    ext x
    obtain ⟨w, rfl⟩ := mk_surjective x
    show mk (cupCocycle (c • z) w) = c • mk (cupCocycle z w)
    rw [← mk_smul]
    exact congrArg mk (Subtype.ext (cup_smul_left _ _ _))

/-- **The cup product `H²(X;ℤ₂) × H²(X;ℤ₂) → H⁴(X;ℤ₂)`**. -/
def cupH22 : Cohomology X 2 →ₗ[ZMod 2] Cohomology X 2 →ₗ[ZMod 2] Cohomology X 4 :=
  Submodule.liftQ _ cupH22Aux (by
    rintro ⟨z, hz⟩ hmem
    obtain ⟨a, ha⟩ : ∃ a : Cochain X 1, d X 1 a = z := hmem
    ext x
    obtain ⟨w, rfl⟩ := mk_surjective x
    show mk (cupCocycle ⟨z, hz⟩ w) = 0
    rw [mk_eq_zero_iff]
    refine ⟨cup a (w : Cochain X 2), ?_⟩
    rw [← cup_delta_left_22 a w.2, ha]
    rfl)

@[simp] theorem cupH22_mk_mk (z w : cocycles X 2) :
    cupH22 (mk z) (mk w) = mk (cupCocycle z w) := rfl

/-- The cup square `H² → H⁴`, `x ↦ x ⌣ x`; this is the top squaring operation used by the
Wu-class route in dimension four. -/
def cupSquare2 (x : Cohomology X 2) : Cohomology X 4 := cupH22 x x

@[simp] theorem cupSquare2_mk (z : cocycles X 2) :
    cupSquare2 (mk z) = mk (cupCocycle z z) := rfl

/-- Bilinear expansion of the degree-two cup square.  This is *only* the polarization identity
coming from bilinearity; graded commutativity of the cup product (which would let one collapse
the two cross terms) is **not** proved in this task. -/
theorem cupSquare2_expand (x y : Cohomology X 2) :
    cupSquare2 (x + y) = cupSquare2 x + cupH22 x y + cupH22 y x + cupSquare2 y := by
  simp only [cupSquare2, map_add, LinearMap.add_apply]
  abel

end Mod2Cohomology
