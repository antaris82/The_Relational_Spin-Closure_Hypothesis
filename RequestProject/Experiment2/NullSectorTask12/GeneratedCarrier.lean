import RequestProject.Experiment2.NullSectorTask12.LeftCarrier

/-!
# Task 12, Layer 2: generated left carriers (§9–§12)

For an arbitrary element `ψ : W` the *generated carrier* is

```
Lgen ψ := { x ⋆ ψ | x : W }
```

which is a real subspace because the product is bilinear.  It is proved left-stable, it
contains `ψ`, and it is the smallest left carrier containing `ψ`.

Following §10 no equation is *assumed* for a generator.  Instead the question "which
algebraic condition on a generator makes the generated carrier small?" is answered by a
derivation: the inherited central quadratic datum satisfies a two-term relation
(`sq_relation`), and from it the self-product condition `e ⋆ e = e` — together with the
exact coordinate values `e 0 = 1/2`, `e 7 = 0` — is *derived* for a suitable generator of
any generated carrier whose central quadratic datum vanishes.

Status: DERIVED throughout.  AXIS-INDEPENDENT: the distinguished axis `A` is not used.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09

/-! ## The generated carrier -/

/-- **§12.  GENERATED CARRIER.**  The set of all left multiples of `ψ`. -/
noncomputable def Lgen (ψ : W) : Submodule ℝ W := LinearMap.range (Rmul ψ)

theorem mem_Lgen_iff (ψ y : W) : y ∈ Lgen ψ ↔ ∃ x : W, x ⋆ ψ = y := by
  simp [Lgen, LinearMap.mem_range]

theorem mul_mem_Lgen (x ψ : W) : x ⋆ ψ ∈ Lgen ψ := ⟨x, rfl⟩

theorem self_mem_Lgen (ψ : W) : ψ ∈ Lgen ψ := ⟨w1, one_mul_W ψ⟩

/-- **§12.  The generated carrier is left-stable.** -/
theorem isLeftCarrier_Lgen (ψ : W) : IsLeftCarrier (Lgen ψ) := by
  rintro x y ⟨z, rfl⟩
  exact ⟨x ⋆ z, (mul_assoc_W x z ψ)⟩

/-- The generated carrier is the smallest left carrier containing its generator. -/
theorem Lgen_le {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W} (hψ : ψ ∈ L) :
    Lgen ψ ≤ L := by
  rintro y ⟨x, rfl⟩
  exact hL x ψ hψ

theorem Lgen_zero : Lgen (0 : W) = ⊥ := by
  ext y
  simp only [mem_Lgen_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨x, rfl⟩; exact mul_zero_W x
  · rintro rfl; exact ⟨0, mul_zero_W 0⟩

theorem Lgen_ne_bot {ψ : W} (hψ : ψ ≠ 0) : Lgen ψ ≠ ⊥ := by
  intro h
  exact hψ (by simpa [h] using self_mem_Lgen ψ)

/-- An invertible generator generates everything. -/
theorem Lgen_eq_top_of_hasInverse {ψ : W} (h : HasInverse ψ) : Lgen ψ = ⊤ := by
  obtain ⟨y, -, hy⟩ := h
  ext z
  simp only [Submodule.mem_top, iff_true, mem_Lgen_iff]
  exact ⟨z ⋆ y, by rw [mul_assoc_W, hy, mul_one_W]⟩

/-! ## The two-term relation for the square of an element -/

/-- Multiplication by a central element, in coordinates. -/
theorem zsmul_mul (a b : ℝ) (x : W) :
    (a • w1 + b • wS) ⋆ x = a • x + b • (wS ⋆ x) := by
  rw [add_mul_W, smul_mul_W, smul_mul_W, one_mul_W]

/-- **DERIVED (§10).**  The two-term relation satisfied by every element of the
inherited carrier: its square is a central combination of itself and the inherited
central quadratic datum.  Nothing is assumed; this is a coordinate identity. -/
theorem sq_relation (x : W) :
    x ⋆ x + Ncand 1 x = (2 * x 0) • x + (2 * x 7) • (wS ⋆ x) := by
  funext i
  fin_cases i <;> simp [Ncand, nRe, nSc, w1, wS, wit8MulFun] <;> ring

/-! ## Elements with a nonzero unit coordinate -/

/-- The coordinate reflection used to produce, out of a nonzero element, a left multiple
with nonzero unit coordinate. -/
def xflipFun (x : W) : W := ![x 0, x 1, x 2, x 3, -x 4, -x 5, -x 6, -x 7]

theorem xflip_mul_coord_0 (x : W) :
    (xflipFun x ⋆ x) 0
      = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2 := by
  simp [xflipFun]; ring

theorem eq_zero_of_coords {x : W} (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0)
    (h3 : x 3 = 0) (h4 : x 4 = 0) (h5 : x 5 = 0) (h6 : x 6 = 0) (h7 : x 7 = 0) :
    x = 0 := by
  funext i
  fin_cases i <;> assumption

/-- **DERIVED.**  Every nonzero element has a left multiple with nonzero unit
coordinate. -/
theorem exists_mul_unit_coord_ne_zero {ψ : W} (hψ : ψ ≠ 0) :
    ∃ x : W, (x ⋆ ψ) 0 ≠ 0 := by
  refine ⟨xflipFun ψ, ?_⟩
  rw [xflip_mul_coord_0]
  intro hz
  refine hψ (eq_zero_of_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
    nlinarith [sq_nonneg (ψ 0), sq_nonneg (ψ 1), sq_nonneg (ψ 2), sq_nonneg (ψ 3),
      sq_nonneg (ψ 4), sq_nonneg (ψ 5), sq_nonneg (ψ 6), sq_nonneg (ψ 7)]

/-! ## Derived self-product generators -/

/-- **NEUTRAL NAME.**  The self-product condition.  It is never assumed of a generator;
it is derived where it is used (§10). -/
def IsSelfProduct (e : W) : Prop := e ⋆ e = e

/-- **DERIVED.**  A nonzero self-product element whose central quadratic datum vanishes
has unit coordinate `1/2` and vanishing central coordinate. -/
theorem selfProduct_coords {e : W} (hidem : IsSelfProduct e) (hne : e ≠ 0)
    (hnull : IsNullElt e) : e 0 = 1 / 2 ∧ e 7 = 0 := by
  have hN : Ncand 1 e = 0 := (isNullElt_iff_Ncand e).1 hnull
  have hrel := sq_relation e
  rw [hidem, hN, add_zero] at hrel
  have hd : ((2 * e 0 - 1) • w1 + (2 * e 7) • wS) ⋆ e = 0 := by
    rw [zsmul_mul, sub_smul, one_smul,
      show ((2 * e 0) • e - e + (2 * e 7) • (wS ⋆ e) : W)
        = ((2 * e 0) • e + (2 * e 7) • (wS ⋆ e)) - e from by abel,
      ← hrel, sub_self]
  by_contra hcon
  have hne2 : ¬ (2 * e 0 - 1 = 0 ∧ 2 * e 7 = 0) := by
    rintro ⟨h1, h2⟩
    exact hcon ⟨by linarith, by linarith⟩
  refine hne ?_
  have hz := congrArg (fun y : W => zinv (2 * e 0 - 1) (2 * e 7) ⋆ y) hd
  simp only [mul_zero_W] at hz
  rwa [← mul_assoc_W, zinv_spec' hne2, one_mul_W] at hz

/-- A central rescaling of an element satisfying a two-term relation is a self-product
element.  Only associativity, centrality and the relation are used. -/
theorem scaled_selfProduct {φ c d : W} (hd : d ∈ Z) (hdc : d ⋆ c = w1)
    (hsq : φ ⋆ φ = c ⋆ φ) : IsSelfProduct (d ⋆ φ) := by
  show (d ⋆ φ) ⋆ (d ⋆ φ) = d ⋆ φ
  calc (d ⋆ φ) ⋆ (d ⋆ φ) = d ⋆ ((φ ⋆ d) ⋆ φ) := by
        rw [mul_assoc_W, ← mul_assoc_W φ]
    _ = d ⋆ ((d ⋆ φ) ⋆ φ) := by rw [← Z_central hd φ]
    _ = d ⋆ (d ⋆ (φ ⋆ φ)) := by rw [mul_assoc_W]
    _ = d ⋆ ((d ⋆ c) ⋆ φ) := by rw [hsq, mul_assoc_W]
    _ = d ⋆ φ := by rw [hdc, one_mul_W]

theorem scaled_ne_zero {φ c d : W} (hd : d ∈ Z) (hdc : d ⋆ c = w1) (hφ : φ ≠ 0) :
    d ⋆ φ ≠ 0 := by
  intro hzero
  refine hφ ?_
  have hcd : c ⋆ d = w1 := by rw [← Z_central hd c]; exact hdc
  have hz := congrArg (fun y : W => c ⋆ y) hzero
  simp only [mul_zero_W] at hz
  rwa [← mul_assoc_W, hcd, one_mul_W] at hz

theorem null_mul {x y : W} (hy : IsNullElt y) : IsNullElt (x ⋆ y) := by
  have hmul : Ncand 1 (x ⋆ y) = Ncand 1 x ⋆ Ncand 1 y := Ncand_mul 1 (by norm_num) x y
  rw [(isNullElt_iff_Ncand y).1 hy, mul_zero_W] at hmul
  exact (isNullElt_iff_Ncand _).2 hmul

/-- **DERIVED (§10, §11).**  Every nonzero generated carrier whose generator has
vanishing central quadratic datum contains a self-product element with the exact
coordinates `e 0 = 1/2`, `e 7 = 0`.  Idempotency is *not* assumed: it is produced. -/
theorem exists_selfProduct_generator {ψ : W} (hψ : ψ ≠ 0) (hnull : IsNullElt ψ) :
    ∃ e : W, e ∈ Lgen ψ ∧ IsSelfProduct e ∧ e ≠ 0 ∧ IsNullElt e ∧
      e 0 = 1 / 2 ∧ e 7 = 0 := by
  obtain ⟨x, hx⟩ := exists_mul_unit_coord_ne_zero hψ
  set φ : W := x ⋆ ψ with hφdef
  have hφnull : IsNullElt φ := null_mul hnull
  have hφne : φ ≠ 0 := by
    intro h
    exact hx (by rw [h]; rfl)
  have hc : ¬ (2 * φ 0 = 0 ∧ 2 * φ 7 = 0) := by
    rintro ⟨h1, -⟩
    exact hx (by linarith)
  set c : W := (2 * φ 0) • w1 + (2 * φ 7) • wS with hcdef
  set d : W := zinv (2 * φ 0) (2 * φ 7) with hddef
  have hdZ : d ∈ Z := smul_add_smul_mem_Z _ _
  have hdc : d ⋆ c = w1 := zinv_spec' hc
  have hsq : φ ⋆ φ = c ⋆ φ := by
    have hrel := sq_relation φ
    rw [(isNullElt_iff_Ncand φ).1 hφnull, add_zero] at hrel
    rw [hcdef, zsmul_mul]
    exact hrel
  have hidem : IsSelfProduct (d ⋆ φ) := scaled_selfProduct hdZ hdc hsq
  have hne : d ⋆ φ ≠ 0 := scaled_ne_zero hdZ hdc hφne
  have hnull' : IsNullElt (d ⋆ φ) := null_mul hφnull
  obtain ⟨c0, c7⟩ := selfProduct_coords hidem hne hnull'
  exact ⟨d ⋆ φ, isLeftCarrier_Lgen ψ d φ (mul_mem_Lgen x ψ), hidem, hne, hnull', c0, c7⟩

/-! ## Central self-products and the dichotomy for self-product elements -/

/-- **DERIVED.**  A central self-product element is `0` or the unit. -/
theorem central_selfProduct_dichotomy {z : W} (hz : z ∈ Z) (h : z ⋆ z = z) :
    z = 0 ∨ z = w1 := by
  obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 hz
  rw [central_mul_rule] at h
  obtain ⟨h1, h2⟩ := Z_coeff_unique h
  have hb : b = 0 := by
    rcases mul_eq_zero.1 (show b * (2 * a - 1) = 0 by nlinarith) with hb | ha
    · exact hb
    · exfalso; nlinarith [sq_nonneg b]
  subst hb
  rcases mul_eq_zero.1 (show a * (a - 1) = 0 by nlinarith) with ha | ha
  · left; rw [ha]; simp
  · right; rw [show a = 1 by linarith]; simp

/-- **DERIVED.**  Every self-product element either has vanishing central quadratic datum
or is the unit itself. -/
theorem selfProduct_dichotomy {e : W} (h : IsSelfProduct e) : IsNullElt e ∨ e = w1 := by
  have hmul : Ncand 1 (e ⋆ e) = Ncand 1 e ⋆ Ncand 1 e := Ncand_mul 1 (by norm_num) e e
  rw [h] at hmul
  rcases central_selfProduct_dichotomy (Ncand_mem 1 e) hmul.symm with h0 | h1
  · exact Or.inl ((isNullElt_iff_Ncand e).2 h0)
  · right
    have hinv : HasInverse e := (hasInverse_iff e).2 (by
      rw [isNullElt_iff_Ncand, h1]
      intro hc
      have : (w1 : W) 0 = (0 : W) 0 := by rw [hc]
      simp [w1] at this)
    obtain ⟨y, -, hy⟩ := hinv
    calc e = w1 ⋆ e := (one_mul_W e).symm
      _ = (y ⋆ e) ⋆ e := by rw [hy]
      _ = y ⋆ (e ⋆ e) := mul_assoc_W y e e
      _ = y ⋆ e := by rw [h]
      _ = w1 := hy

/-! ## Self-product elements from square roots of the unit -/

/-- The half-sum construction: for any `m` with `m ⋆ m = w1` this is a self-product
element. -/
noncomputable def halfSum (m : W) : W := (1 / 2 : ℝ) • (w1 + m)

theorem halfSum_selfProduct {m : W} (hm : m ⋆ m = w1) : IsSelfProduct (halfSum m) := by
  show halfSum m ⋆ halfSum m = halfSum m
  rw [halfSum, smul_mul_W, mul_smul_W, add_mul_W, mul_add_W, mul_add_W,
    one_mul_W w1, one_mul_W m, mul_one_W m, hm]
  module

theorem halfSum_coord_7 (m : W) : halfSum m 7 = (1 / 2 : ℝ) * m 7 := by
  have hw : (w1 : W) 7 = 0 := rfl
  simp only [halfSum, Pi.smul_apply, Pi.add_apply, hw, smul_eq_mul, zero_add]

theorem halfSum_coord_0 (m : W) : halfSum m 0 = (1 / 2 : ℝ) * (1 + m 0) := by
  have hw : (w1 : W) 0 = 1 := rfl
  simp only [halfSum, Pi.smul_apply, Pi.add_apply, hw, smul_eq_mul]

end NullSectorTask12
