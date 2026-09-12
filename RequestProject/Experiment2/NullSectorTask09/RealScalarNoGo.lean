import RequestProject.Experiment2.NullSectorTask09.SafeBase

/-!
# Task 09, Layer 1: Phase A — the real-valued negative control

An entirely unknown map `NR : W → ℝ` is tested.  Only three properties are
required:

* `IsRealQuadratic NR` (degree-two real homogeneity + bilinear polarization);
* `MultiplicativeR NR` (`NR (x ⋆ y) = NR x * NR y`);
* `ExtendsQ4R NR` (`NR (ι₃ X) = Q4 X` for every old vector `X`).

No such map is assumed to exist.  The values of `NR` on the eight derived
Task-08 basis elements are *derived* and then shown to be inconsistent.

**Status: SCALAR CODOMAIN OBSTRUCTION.**
-/

namespace NullSectorTask09

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08

/-- **PHASE A hypothesis set.**  Real-quadratic, multiplicative, and restricting
to the inherited Lorentz form on the embedded old carrier. -/
structure AdmissibleR (NR : W → ℝ) : Prop where
  quad : IsRealQuadratic NR
  mul : MultiplicativeR NR
  ext : ExtendsQ4R NR

namespace AdmissibleR

variable {NR : W → ℝ} (h : AdmissibleR NR)
include h

/-! ## Inherited values, forced by the old-`Q4` restriction -/

theorem val_w1 : NR w1 = 1 := by
  have hx := h.ext e₀
  rwa [iota3_e₀, Q4_e₀] at hx

theorem val_wA : NR wA = -1 := by
  have hx := h.ext dirA
  rwa [iota3_dirA, Q4_dirA] at hx

theorem val_wB : NR wB = -1 := by
  have hx := h.ext dirB
  rwa [iota3_dirB, Q4_dirB] at hx

theorem val_wC : NR wC = -1 := by
  have hx := h.ext dirC
  rwa [iota3_dirC, Q4_dirC] at hx

/-! ## Values forced by multiplicativity together with the derived Task-08
multiplication relations -/

theorem val_wP : NR wP = 1 := by
  have hx := h.mul wA wB
  rw [wit8_wA_wB, h.val_wA, h.val_wB] at hx
  linarith

theorem val_wQ : NR wQ = 1 := by
  have hx := h.mul wA wC
  rw [wit8_wA_wC, h.val_wA, h.val_wC] at hx
  linarith

theorem val_wR : NR wR = 1 := by
  have hx := h.mul wB wC
  rw [wit8_wB_wC, h.val_wB, h.val_wC] at hx
  linarith

theorem val_wS : NR wS = -1 := by
  have hx := h.mul wP wC
  rw [wit8_wP_wC, h.val_wP, h.val_wC] at hx
  linarith

/-- **DERIVED, PHASE A.**  Every value on the eight derived Task-08 basis
elements is forced. -/
theorem forced_values :
    NR w1 = 1 ∧ NR wA = -1 ∧ NR wB = -1 ∧ NR wC = -1 ∧
      NR wP = 1 ∧ NR wQ = 1 ∧ NR wR = 1 ∧ NR wS = -1 :=
  ⟨h.val_w1, h.val_wA, h.val_wB, h.val_wC, h.val_wP, h.val_wQ, h.val_wR, h.val_wS⟩

end AdmissibleR

/-! ## The obstruction element -/

/-- The two-term combination used by the obstruction.  Its square in the
inherited product is `2 • S`. -/
theorem sq_one_add_wS : (w1 + wS) ⋆ (w1 + wS) = (2 : ℝ) • wS := by
  rw [mul_add_W, add_mul_W, add_mul_W, one_mul_W, one_mul_W, mul_one_W, wS_sq]
  module

/-- **MINIMAL SCALAR OBSTRUCTION.**  No real-valued map can be simultaneously
degree-two homogeneous, multiplicative, and take the inherited value `-1` on the
three embedded old spatial directions.  Neither the bilinearity of the
polarization nor the value on the unit is needed: the smallest transparent
configuration uses only

```
NR A = NR B = NR C = -1      (old Q4 restriction)
NR (x ⋆ y) = NR x * NR y     (multiplicativity)
NR (r • x) = r² * NR x       (quadratic homogeneity)
```

together with the reality of the codomain (`z² ≥ 0`), applied to the single
element `1 + S`. -/
theorem scalar_obstruction_minimal (NR : W → ℝ)
    (hhom : ∀ (r : ℝ) (x : W), NR (r • x) = r ^ 2 * NR x)
    (hmul : MultiplicativeR NR)
    (hA : NR wA = -1) (hB : NR wB = -1) (hC : NR wC = -1) : False := by
  -- the two mixed channels needed
  have hP : NR wP = 1 := by
    have hx := hmul wA wB; rw [wit8_wA_wB, hA, hB] at hx; linarith
  have hS : NR wS = -1 := by
    have hx := hmul wP wC; rw [wit8_wP_wC, hP, hC] at hx; linarith
  -- the obstruction element
  have h1 : NR ((w1 + wS) ⋆ (w1 + wS)) = NR (w1 + wS) * NR (w1 + wS) :=
    hmul (w1 + wS) (w1 + wS)
  have h2 : NR ((w1 + wS) ⋆ (w1 + wS)) = -4 := by
    rw [sq_one_add_wS, hhom, hS]; norm_num
  nlinarith [sq_nonneg (NR (w1 + wS)), h1, h2]

/-- **PHASE A VERDICT: SCALAR CODOMAIN OBSTRUCTION.**  There is *no*
real-valued quadratic multiplicative extension of the inherited Lorentz form to
the Task-08 associative closure, even though the product carrier has already
been successfully enlarged. -/
theorem no_real_valued_extension : ¬ ∃ NR : W → ℝ, AdmissibleR NR := by
  rintro ⟨NR, h⟩
  refine scalar_obstruction_minimal NR (fun r x => ?_) h.mul h.val_wA h.val_wB h.val_wC
  have := h.quad.homog r x
  simpa [smul_eq_mul] using this

/-- The same verdict spelled out in unfolded form. -/
theorem no_real_valued_extension_explicit :
    ¬ ∃ NR : W → ℝ,
        IsRealQuadratic NR ∧ MultiplicativeR NR ∧ ExtendsQ4R NR := by
  rintro ⟨NR, hq, hm, he⟩
  exact no_real_valued_extension ⟨NR, ⟨hq, hm, he⟩⟩

/-- **THE EXACT INCOMPATIBLE EQUATIONS.**  For an admissible real-valued map the
following five statements hold simultaneously, and the last two are
contradictory over `ℝ`. -/
theorem scalar_incompatible_equations (NR : W → ℝ) (h : AdmissibleR NR) :
    NR wS = -1 ∧
    (w1 + wS) ⋆ (w1 + wS) = (2 : ℝ) • wS ∧
    NR ((2 : ℝ) • wS) = -4 ∧
    NR ((w1 + wS) ⋆ (w1 + wS)) = NR (w1 + wS) * NR (w1 + wS) ∧
    0 ≤ NR (w1 + wS) * NR (w1 + wS) := by
  refine ⟨h.val_wS, sq_one_add_wS, ?_, h.mul _ _, mul_self_nonneg _⟩
  have := h.quad.homog 2 wS
  rw [h.val_wS] at this
  rw [this]
  norm_num

end NullSectorTask09
