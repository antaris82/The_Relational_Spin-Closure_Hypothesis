import RequestProject.Experiment2.NullSectorTask10.VectorChannels

/-!
# Task 10, Layer 5: internal lifts of the axial rotation

Only now, with the algebra automorphism family `Φθ` completely classified, is
the lift question of §16 asked:

> can the same rotation be implemented by multiplication with elements internal
> to the carrier?

An unknown one-parameter family `U : ℝ → W` is sought, subject only to

* `U θ` lies in the already derived real two-plane `K = spanℝ{1, R}` (§17),
* `U 0 = 1`,
* `U (θ + φ) = U θ ⋆ U φ` (whence each `U θ` is invertible, with inverse
  `U (-θ)`),
* `U θ ⋆ x ⋆ U (-θ) = Φθ x` for every `x`.

No formula, and in particular no half-angle, is inserted: the coordinate
functions are *derived* from the group law together with the conjugation action.

## The scalar freedom is a result, not a gap

The derivation below shows that the conjugation action determines `U θ` only up
to a multiplicative scalar function `k`:

```
U θ = k θ • (cos (θ/2) • 1 - sin (θ/2) • R),   k (θ + φ) = k θ * k φ, k 0 = 1, k θ ≠ 0.
```

`k` cancels in the conjugation, so **it cannot be removed by any condition that
only refers to the conjugation action**, and it is not removed here by fiat.  It
is recorded honestly:

* the classification theorem `klift_classification` keeps `k` free, in both
  directions;
* `klift_not_unique` exhibits a genuinely different lift (`k θ = exp θ`), so the
  answer to "is the lift unique after `U 0 = 1`?" is **no**;
* consequently `U (2π) = -k (2π) • 1` in general (`klift_periodicity`): the
  sharp value `-1` holds for the distinguished representative `Ustd`, and every
  statement that uses it carries that hypothesis explicitly.

A *derived* — not postulated — sharpening is proved at the end
(`klift_branch_forces_k`): if the lift is additionally required to preserve the
Task-09 central norm branch under **left multiplication** (a condition
formulated purely in already-established Task-09 data, and *not* in terms of the
conjugation action), then `k ≡ 1` follows, and the distinguished representative
is the unique such lift.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## §17 — the candidate lift carrier `K = spanℝ{1, R}` -/

/-- **THE MINIMAL LIFT CARRIER.**  The already derived real two-plane spanned by
the unit and the transverse product channel `R`, with `R ⋆ R = -1`. -/
def K : Submodule ℝ W := Submodule.span ℝ {w1, wR}

/-- An element of `K` in normal form. -/
noncomputable def ksc (a b : ℝ) : W := a • w1 + b • wR

theorem ksc_mem_K (a b : ℝ) : ksc a b ∈ K := by
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem mem_K_iff (x : W) : x ∈ K ↔ ∃ a b : ℝ, x = ksc a b := by
  rw [K, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, rfl⟩

@[simp] theorem ksc_coord_0 (a b : ℝ) : ksc a b 0 = a := by simp [ksc, w1, wR]
@[simp] theorem ksc_coord_6 (a b : ℝ) : ksc a b 6 = b := by simp [ksc, w1, wR]

/-- The two coefficients of an element of `K` are its two nonzero coordinates. -/
theorem eq_ksc_of_mem_K {x : W} (hx : x ∈ K) : x = ksc (x 0) (x 6) := by
  obtain ⟨a, b, rfl⟩ := (mem_K_iff x).1 hx
  rw [ksc_coord_0, ksc_coord_6]

theorem ksc_injective {a b a' b' : ℝ} (h : ksc a b = ksc a' b') : a = a' ∧ b = b' := by
  constructor
  · have := congrFun h 0; simpa using this
  · have := congrFun h 6; simpa using this

theorem ksc_smul (r a b : ℝ) : r • ksc a b = ksc (r * a) (r * b) := by
  simp [ksc, smul_add, smul_smul]

/-- **THE INTERNAL MULTIPLICATION OF `K`**, derived from `R ⋆ R = -1`. -/
theorem ksc_mul_ksc (a b c d : ℝ) :
    ksc a b ⋆ ksc c d = ksc (a * c - b * d) (a * d + b * c) := by
  simp only [ksc, add_mul_W, mul_add_W, smul_mul_W, mul_smul_W, one_mul_W,
    mul_one_W, wit8_wR_wR]
  module

theorem ksc_ne_zero {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : ksc a b ≠ 0 := by
  intro hzero
  rcases h with h | h
  · exact h (by have := congrFun hzero 0; simpa using this)
  · exact h (by have := congrFun hzero 6; simpa using this)

/-- Conjugation of the transverse generator `B` by a general element of `K`. -/
theorem ksc_conj_wB (a b p q : ℝ) :
    (ksc a b ⋆ wB) ⋆ ksc p q = (a * p + b * q) • wB + (a * q - b * p) • wC := by
  funext i
  fin_cases i <;> (simp [ksc, wB, wC, wR, w1, wit8MulFun]; try ring1)

/-! ## The lift problem -/

/-- **THE LIFT PROBLEM (§16–17).**  A continuous formula is *not* assumed; only
membership in `K`, the normalization at zero, the one-parameter group law and
the conjugation action. -/
structure IsKLift (U : ℝ → W) : Prop where
  /-- Each member lies in the minimal carrier `K`. -/
  mem : ∀ θ : ℝ, U θ ∈ K
  /-- Normalization. -/
  unit : U 0 = w1
  /-- One-parameter group law; it makes every `U θ` invertible. -/
  group : ∀ θ φ : ℝ, U (θ + φ) = U θ ⋆ U φ
  /-- The conjugation action is the algebra automorphism of Layer 3. -/
  conj : ∀ (θ : ℝ) (x : W), (U θ ⋆ x) ⋆ U (-θ) = Phi θ x

/-! ## Existence: the distinguished representative -/

/-- The distinguished lift.  Its coordinate functions are **derived** in
`klift_classification`; they are written here only in order to exhibit a
witness. -/
noncomputable def Ustd (θ : ℝ) : W := ksc (Real.cos (θ / 2)) (- Real.sin (θ / 2))

@[simp] theorem Ustd_zero : Ustd 0 = w1 := by
  simp [Ustd, ksc]

theorem Ustd_ne_zero (θ : ℝ) : Ustd θ ≠ 0 := by
  apply ksc_ne_zero
  by_cases h : Real.cos (θ / 2) = 0
  · right
    intro hs
    have hs' : Real.sin (θ / 2) = 0 := by linarith [neg_eq_zero.1 hs]
    have := Real.sin_sq_add_cos_sq (θ / 2)
    rw [h, hs'] at this
    norm_num at this
  · exact Or.inl h

theorem Ustd_group (θ φ : ℝ) : Ustd (θ + φ) = Ustd θ ⋆ Ustd φ := by
  rw [Ustd, Ustd, Ustd, ksc_mul_ksc]
  have hhalf : (θ + φ) / 2 = θ / 2 + φ / 2 := by ring
  rw [hhalf, Real.cos_add, Real.sin_add]
  congr 1
  · ring
  · ring

theorem Ustd_neg (θ : ℝ) : Ustd (-θ) = ksc (Real.cos (θ / 2)) (Real.sin (θ / 2)) := by
  rw [Ustd]
  congr 1
  · rw [show (-θ) / 2 = -(θ / 2) by ring, Real.cos_neg]
  · rw [show (-θ) / 2 = -(θ / 2) by ring, Real.sin_neg, neg_neg]

/-! ### The conjugation computation, for abstract coefficients -/

/-- The rotation of the carrier written with explicit cosine/sine data. -/
def PhiCSFun (c s : ℝ) (x : W) : W :=
  ![x 0, x 1, c * x 2 - s * x 3, s * x 2 + c * x 3,
    c * x 4 - s * x 5, s * x 4 + c * x 5, x 6, x 7]

theorem Phi_eq_PhiCS (θ : ℝ) (x : W) : Phi θ x = PhiCSFun (Real.cos θ) (Real.sin θ) x := by
  funext i
  fin_cases i <;> simp [PhiCSFun, Phi, PhiFun]

/-- **THE CONJUGATION FORMULA.**  For an arbitrary normalized element of `K`,
conjugation is the rotation with the *doubled* angle data.  This is where the
half-angle appears; it is computed, not assumed. -/
theorem conj_coords (a b : ℝ) (hab : a * a + b * b = 1) (x : W) :
    (ksc a b ⋆ x) ⋆ ksc a (-b) = PhiCSFun (a * a - b * b) (-(2 * a * b)) x := by
  funext i
  fin_cases i <;>
    simp [ksc, w1, wR, PhiCSFun, wit8MulFun] <;>
    first
      | ring1
      | linear_combination (x 0) * hab
      | linear_combination (x 1) * hab
      | linear_combination (x 6) * hab
      | linear_combination (x 7) * hab

theorem Ustd_conj (θ : ℝ) (x : W) : (Ustd θ ⋆ x) ⋆ Ustd (-θ) = Phi θ x := by
  have hab : Real.cos (θ / 2) * Real.cos (θ / 2)
      + (- Real.sin (θ / 2)) * (- Real.sin (θ / 2)) = 1 := by
    have := Real.sin_sq_add_cos_sq (θ / 2); nlinarith [this]
  have hneg : Ustd (-θ) = ksc (Real.cos (θ / 2)) (-(- Real.sin (θ / 2))) := by
    rw [Ustd_neg]; congr 1; ring
  have hcos := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ from by ring] at hcos
  have hsin := Real.sin_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ from by ring] at hsin
  have hp := Real.sin_sq_add_cos_sq (θ / 2)
  rw [Ustd, hneg, conj_coords _ _ hab, Phi_eq_PhiCS]
  congr 1
  · rw [hcos]; nlinarith [hp]
  · rw [hsin]; ring

/-- **EXISTENCE OF AN INTERNAL LIFT INSIDE `K`.** -/
theorem Ustd_isKLift : IsKLift Ustd where
  mem _ := ksc_mem_K _ _
  unit := Ustd_zero
  group := Ustd_group
  conj := Ustd_conj

/-! ## §18 — exact classification of the internal lifts -/

/-- The scalar freedom left by the conjugation action: an arbitrary
multiplicative, nowhere vanishing, normalized real function. -/
structure IsScalarFactor (k : ℝ → ℝ) : Prop where
  /-- Normalization. -/
  one : k 0 = 1
  /-- Nowhere vanishing. -/
  ne_zero : ∀ θ : ℝ, k θ ≠ 0
  /-- Multiplicativity. -/
  mul : ∀ θ φ : ℝ, k (θ + φ) = k θ * k φ

theorem IsScalarFactor.neg {k : ℝ → ℝ} (hk : IsScalarFactor k) (θ : ℝ) :
    k θ * k (-θ) = 1 := by
  have := hk.mul θ (-θ)
  rw [add_neg_cancel, hk.one] at this
  exact this.symm

/-- Every scalar factor is a square, hence strictly positive. -/
theorem IsScalarFactor.pos {k : ℝ → ℝ} (hk : IsScalarFactor k) (θ : ℝ) : 0 < k θ := by
  have h := hk.mul (θ / 2) (θ / 2)
  rw [show θ / 2 + θ / 2 = θ from by ring] at h
  rw [h]
  exact mul_self_pos.2 (hk.ne_zero (θ / 2))

/-- **EVERY SCALAR FACTOR GIVES A LIFT.** -/
theorem klift_of_scalarFactor {k : ℝ → ℝ} (hk : IsScalarFactor k) :
    IsKLift (fun θ => k θ • Ustd θ) where
  mem θ := Submodule.smul_mem _ _ (ksc_mem_K _ _)
  unit := by simp [hk.one]
  group θ φ := by
    rw [hk.mul, Ustd_group, smul_mul_W, mul_smul_W, smul_smul]
  conj θ x := by
    rw [smul_mul_W, mul_smul_W, smul_mul_W, smul_smul, Ustd_conj,
      show k (-θ) * k θ = 1 from by rw [mul_comm]; exact hk.neg θ, one_smul]

/-- **THE CLASSIFICATION (§18).**  Every internal lift inside `K` is the
distinguished one up to a multiplicative scalar function, and conversely.  The
coordinate functions — in particular the half angle — are derived from the group
law and the conjugation action alone. -/
theorem klift_classification (U : ℝ → W) :
    IsKLift U ↔ ∃ k : ℝ → ℝ, IsScalarFactor k ∧ ∀ θ, U θ = k θ • Ustd θ := by
  constructor
  · intro hU
    set A : ℝ → ℝ := fun θ => U θ 0 with hA
    set B : ℝ → ℝ := fun θ => U θ 6 with hB
    have hUksc : ∀ θ, U θ = ksc (A θ) (B θ) := by
      intro θ
      have h := eq_ksc_of_mem_K (hU.mem θ)
      simpa [hA, hB] using h
    -- the group law at `(θ, -θ)`
    have hinv : ∀ θ, A θ * A (-θ) - B θ * B (-θ) = 1 ∧
        A θ * B (-θ) + B θ * A (-θ) = 0 := by
      intro θ
      have h := hU.group θ (-θ)
      rw [add_neg_cancel, hU.unit, hUksc θ, hUksc (-θ), ksc_mul_ksc] at h
      have h' : ksc (1 : ℝ) 0 = ksc (A θ * A (-θ) - B θ * B (-θ))
          (A θ * B (-θ) + B θ * A (-θ)) := by
        rw [← h]; simp [ksc]
      obtain ⟨e1, e2⟩ := ksc_injective h'
      exact ⟨e1.symm, e2.symm⟩
    -- the conjugation condition on the transverse generator
    have hconjB : ∀ θ, A θ * A (-θ) + B θ * B (-θ) = Real.cos θ ∧
        A θ * B (-θ) - B θ * A (-θ) = Real.sin θ := by
      intro θ
      have h := hU.conj θ wB
      rw [hUksc θ, hUksc (-θ), ksc_conj_wB, Phi_wB] at h
      have h2 := congrFun h 2
      have h3 := congrFun h 3
      simp [wB, wC] at h2 h3
      exact ⟨h2, h3⟩
    -- solving the four bilinear equations
    have hm : ∀ θ, A θ * (A (-θ) * Real.cos (θ / 2) + B (-θ) * Real.sin (θ / 2))
          = Real.cos (θ / 2) ∧
        B θ * (A (-θ) * Real.cos (θ / 2) + B (-θ) * Real.sin (θ / 2))
          = -Real.sin (θ / 2) := by
      intro θ
      obtain ⟨h1, h2⟩ := hinv θ
      obtain ⟨h3, h4⟩ := hconjB θ
      have hp := Real.sin_sq_add_cos_sq (θ / 2)
      have hcos := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ from by ring] at hcos
      have hsin := Real.sin_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ from by ring] at hsin
      have hap : A θ * A (-θ) = Real.cos (θ / 2) ^ 2 := by linarith
      have hbq : B θ * B (-θ) = -Real.sin (θ / 2) ^ 2 := by linarith
      have haq : A θ * B (-θ) = Real.sin (θ / 2) * Real.cos (θ / 2) := by linarith
      have hbp : B θ * A (-θ) = -(Real.sin (θ / 2) * Real.cos (θ / 2)) := by linarith
      constructor
      · linear_combination Real.cos (θ / 2) * hap + Real.sin (θ / 2) * haq
          + Real.cos (θ / 2) * hp
      · linear_combination Real.cos (θ / 2) * hbp + Real.sin (θ / 2) * hbq
          - Real.sin (θ / 2) * hp
    have hmne : ∀ θ, A (-θ) * Real.cos (θ / 2) + B (-θ) * Real.sin (θ / 2) ≠ 0 := by
      intro θ h0
      obtain ⟨g1, g2⟩ := hm θ
      rw [h0, mul_zero] at g1 g2
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2), g1, g2]
    have hUform : ∀ θ, U θ =
        (A (-θ) * Real.cos (θ / 2) + B (-θ) * Real.sin (θ / 2))⁻¹ • Ustd θ := by
      intro θ
      obtain ⟨g1, g2⟩ := hm θ
      rw [hUksc θ, Ustd, ksc_smul]
      congr 1
      · rw [inv_mul_eq_div, eq_div_iff (hmne θ)]; exact g1
      · rw [inv_mul_eq_div, eq_div_iff (hmne θ)]; exact g2
    have hA0 : A 0 = 1 := by simp [hA, hU.unit, w1]
    refine ⟨fun θ => (A (-θ) * Real.cos (θ / 2) + B (-θ) * Real.sin (θ / 2))⁻¹,
      ⟨?_, ?_, ?_⟩, hUform⟩
    · simp [hA0]
    · intro θ; exact inv_ne_zero (hmne θ)
    · intro θ φ
      have h := hU.group θ φ
      rw [hUform θ, hUform φ, hUform (θ + φ), smul_mul_W, mul_smul_W, smul_smul,
        ← Ustd_group] at h
      exact smul_left_injective ℝ (Ustd_ne_zero (θ + φ)) h
  · rintro ⟨k, hk, hU⟩
    have : U = fun θ => k θ • Ustd θ := funext hU
    rw [this]
    exact klift_of_scalarFactor hk

/-! ## §19 — periodicity of the internal lift -/

@[simp] theorem Ustd_two_pi : Ustd (2 * Real.pi) = -w1 := by
  have h : 2 * Real.pi / 2 = Real.pi := by ring
  rw [Ustd, h, Real.cos_pi, Real.sin_pi]
  simp [ksc]

@[simp] theorem Ustd_four_pi : Ustd (4 * Real.pi) = w1 := by
  have h : 4 * Real.pi / 2 = 2 * Real.pi := by ring
  rw [Ustd, h, Real.cos_two_pi, Real.sin_two_pi]
  simp [ksc]

/-- **THE `2π`/`4π` VALUES OF AN ARBITRARY INTERNAL LIFT.**  The scalar freedom
is *not* removed: only the shape `U (2π) = -c • 1`, `U (4π) = c² • 1` with
`c ≠ 0` is forced. -/
theorem klift_periodicity {U : ℝ → W} (hU : IsKLift U) :
    ∃ c : ℝ, 0 < c ∧ U (2 * Real.pi) = (-c) • w1 ∧ U (4 * Real.pi) = (c ^ 2) • w1 := by
  obtain ⟨k, hk, hUk⟩ := (klift_classification U).1 hU
  refine ⟨k (2 * Real.pi), hk.pos _, ?_, ?_⟩
  · rw [hUk, Ustd_two_pi, smul_neg, neg_smul]
  · have h4 : (4 : ℝ) * Real.pi = 2 * Real.pi + 2 * Real.pi := by ring
    rw [hUk, Ustd_four_pi, h4, hk.mul, sq]

/-- **PERIODICITY OF THE DISTINGUISHED REPRESENTATIVE.** -/
theorem Ustd_periodicity :
    Ustd (2 * Real.pi) = -w1 ∧ Ustd (4 * Real.pi) = w1 :=
  ⟨Ustd_two_pi, Ustd_four_pi⟩

/-! ## The lift is *not* unique -/

theorem exp_isScalarFactor : IsScalarFactor Real.exp where
  one := Real.exp_zero
  ne_zero θ := Real.exp_ne_zero θ
  mul θ φ := Real.exp_add θ φ

/-- **ANSWER TO AUDIT QUESTION 6: NO.**  The normalization `U 0 = 1` together
with the group law and the conjugation action does *not* determine the lift.
An explicitly different lift is exhibited. -/
theorem klift_not_unique : ∃ U : ℝ → W, IsKLift U ∧ U ≠ Ustd := by
  refine ⟨fun θ => Real.exp θ • Ustd θ, klift_of_scalarFactor exp_isScalarFactor, ?_⟩
  intro h
  have h2 := congrFun h (2 * Real.pi)
  rw [Ustd_two_pi] at h2
  have h0 := congrFun h2 0
  simp [w1] at h0

/-! ## A *derived* sharpening: preservation of a Task-09 branch -/

theorem ksc_coords (a b : ℝ) : ksc a b = ![a, 0, 0, 0, 0, 0, b, 0] := by
  funext i; fin_cases i <;> simp [ksc, w1, wR]

@[simp] theorem nRe_ksc (a b : ℝ) : nRe (ksc a b) = a ^ 2 + b ^ 2 := by
  rw [ksc_coords]; simp [nRe]

@[simp] theorem nSc_ksc (a b : ℝ) : nSc (ksc a b) = 0 := by
  rw [ksc_coords]; simp [nSc]

@[simp] theorem nRe_Ustd (θ : ℝ) : nRe (Ustd θ) = 1 := by
  rw [Ustd, nRe_ksc]
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

@[simp] theorem nSc_Ustd (θ : ℝ) : nSc (Ustd θ) = 0 := by
  rw [Ustd, nSc_ksc]

theorem Ncand_coord_0 (z : ℝ) (x : W) : Ncand z x 0 = nRe x := by
  simp [Ncand, w1, wS]

theorem nRe_w1 : nRe w1 = 1 := by
  simp [nRe, w1]

/-- **THE DERIVED NORMALIZATION.**  Requiring the lift to preserve the Task-09
branch `N₊` under *left multiplication* — a condition stated purely in
already-established Task-09 data, and independent of the conjugation action —
forces the scalar factor to be identically `1`, hence singles out the
distinguished representative.  Note that this is an *extra hypothesis*, not a
convention: without it the scalar freedom of `klift_classification` persists. -/
theorem klift_branch_forces_k {U : ℝ → W} (hU : IsKLift U)
    (hbranch : ∀ (θ : ℝ) (ψ : W), Ncand 1 (U θ ⋆ ψ) = Ncand 1 ψ) :
    U = Ustd := by
  obtain ⟨k, hk, hUk⟩ := (klift_classification U).1 hU
  have hk1 : ∀ θ, k θ = 1 := by
    intro θ
    have h := hbranch θ w1
    rw [hUk, mul_one_W] at h
    have h0 := congrFun h 0
    rw [Ncand_coord_0, Ncand_coord_0, nRe_smul, nRe_Ustd, nRe_w1] at h0
    have hpos := hk.pos θ
    nlinarith [h0, hpos]
  funext θ
  rw [hUk, hk1, one_smul]

end NullSectorTask10
