import RequestProject.Experiment2.NullSectorTask11.PeriodicityAudit

/-!
# Task 11, Layer 8: conditional quadratic compatibility (§23–§27)

**CONDITIONAL COMPATIBILITY — NOT INHERITED.**  Nothing in Tasks 08–10 requires
an internal lift to interact with the Task-09 central quadratic branches.  The
predicate defined here is therefore an explicitly *added* structural test, and
every theorem of this module carries it as a hypothesis.  It supports none of
the classification results of Layers 1–7.

Both Task-09 branches `N₊ = Ncand 1` and `N₋ = Ncand (-1)` are retained and
tested symmetrically; neither is selected.  The two branch tests are run through
one branch-parameterized theorem whose only input is the *proved* sign relation
`ζ * ζ = 1`, so the transport between the branches is justified by an
established symmetry rather than by renaming.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## The two inherited branches, under neutral names -/

/-- **INHERITED (Task 09).**  The first central quadratic branch. -/
noncomputable def Nplus : W → W := Ncand 1

/-- **INHERITED (Task 09).**  The second central quadratic branch. -/
noncomputable def Nminus : W → W := Ncand (-1)

theorem Ncand_eq_zc (z : ℝ) (x : W) : Ncand z x = zc (nRe x) (z * nSc x) := rfl

@[simp] theorem nRe_zc (a b : ℝ) : nRe (zc a b) = a ^ 2 - b ^ 2 := by
  simp only [nRe, zc_coord_0, zc_coord_1, zc_coord_2, zc_coord_3, zc_coord_4, zc_coord_5,
    zc_coord_6, zc_coord_7]
  ring

@[simp] theorem nSc_zc (a b : ℝ) : nSc (zc a b) = 2 * (a * b) := by
  simp only [nSc, zc_coord_0, zc_coord_1, zc_coord_2, zc_coord_3, zc_coord_4, zc_coord_5,
    zc_coord_6, zc_coord_7]
  ring

@[simp] theorem nRe_Uref (θ : ℝ) : nRe (Uref θ) = 1 := nRe_Ustd θ

@[simp] theorem nSc_Uref (θ : ℝ) : nSc (Uref θ) = 0 := nSc_Ustd θ

/-! ## §23 — the conditional predicate -/

/-- **CONDITIONAL COMPATIBILITY CONDITION (§23).**  Preservation of a central
quadratic branch under *left multiplication* by the lift.  This is a new
structural test, not an inherited requirement. -/
def PreservesLeftQuadratic (N : W → W) (U : ℝ → W) : Prop :=
  ∀ (θ : ℝ) (x : W), N (U θ ⋆ x) = N x

/-! ## The branch-parameterized criterion -/

/-- **DERIVED CRITERION.**  For a branch parameter with `ζ * ζ = 1`, the
conditional compatibility condition is *equivalent* to the two pointwise
coefficient conditions `nRe (U θ) = 1` and `nSc (U θ) = 0`.  The proof uses only
the inherited multiplicativity of the Task-09 coefficient functions. -/
theorem preservesLeftQuadratic_iff {ζ : ℝ} (hζ : ζ * ζ = 1) (U : ℝ → W) :
    PreservesLeftQuadratic (Ncand ζ) U ↔ ∀ θ, nRe (U θ) = 1 ∧ nSc (U θ) = 0 := by
  constructor
  · intro h θ
    have h1 := h θ w1
    rw [mul_one_W, Ncand_eq_zc, Ncand_eq_zc] at h1
    obtain ⟨e1, e2⟩ := zc_injective h1
    have hw1 : nRe w1 = 1 := by simp [nRe, w1]
    have hw2 : nSc w1 = 0 := by simp [nSc, w1]
    refine ⟨by rw [e1, hw1], ?_⟩
    rw [hw2, mul_zero] at e2
    rcases mul_eq_zero.1 e2 with h0 | h0
    · exfalso; rw [h0] at hζ; norm_num at hζ
    · exact h0
  · intro h θ x
    obtain ⟨h1, h2⟩ := h θ
    rw [Ncand_eq_zc, Ncand_eq_zc, nRe_mul, nSc_mul, h1, h2]
    congr 1 <;> ring

/-! ## §24 — the `N₊` classification -/

/-- **`N₊` CONDITIONAL CLASSIFICATION (§24).**  Among the continuous full lifts,
exactly one satisfies the `N₊` test, namely the reference lift; equivalently both
continuous parameters are forced to vanish.  The reference lift is *proved* to
satisfy the condition, not assumed to. -/
theorem Nplus_compatibility_classification {U : ℝ → W} (hU : IsContinuousFullLift U) :
    PreservesLeftQuadratic Nplus U ↔ U = Uref := by
  obtain ⟨α, β, hUf⟩ := (continuousFullLift_classification U).1 hU
  have hcoeff : ∀ θ, nRe (U θ) = Real.exp (α * θ) ^ 2 * Real.cos (β * θ) ^ 2
      - Real.exp (α * θ) ^ 2 * Real.sin (β * θ) ^ 2 ∧
      nSc (U θ) = 2 * (Real.exp (α * θ) * Real.cos (β * θ) *
        (Real.exp (α * θ) * Real.sin (β * θ))) := by
    intro θ
    rw [hUf, nRe_mul, nSc_mul, nRe_Uref, nSc_Uref, zexp]
    constructor
    · rw [nRe_zc, nSc_zc]; ring
    · rw [nRe_zc, nSc_zc]; ring
  constructor
  · intro hpres
    have hcrit := (preservesLeftQuadratic_iff (ζ := 1) (by norm_num) U).1 hpres
    -- the `S` coefficient forces the rotation parameter to vanish
    have hsin : ∀ θ : ℝ, Real.sin (β * θ) = 0 := by
      intro θ
      have h := (hcrit θ).2
      rw [(hcoeff θ).2] at h
      have hexp : Real.exp (α * θ) ^ 2 ≠ 0 := pow_ne_zero _ (Real.exp_ne_zero _)
      have hprod : Real.exp (α * θ) ^ 2 * (Real.cos (β * θ) * Real.sin (β * θ)) = 0 := by
        linear_combination h / 2
      have hcos : Real.cos (β * θ) * Real.sin (β * θ) = 0 :=
        (mul_eq_zero.1 hprod).resolve_left hexp
      rcases mul_eq_zero.1 hcos with h0 | h0
      · -- if the cosine vanishes the unit coefficient becomes negative
        exfalso
        have h1 := (hcrit θ).1
        rw [(hcoeff θ).1, h0] at h1
        have hpy := Real.sin_sq_add_cos_sq (β * θ)
        rw [h0] at hpy
        have hs : Real.sin (β * θ) ^ 2 = 1 := by linarith
        nlinarith [Real.exp_pos (α * θ), h1, hs]
      · exact h0
    have hβ : β = 0 := by
      by_contra hne
      have h := hsin (Real.pi / (2 * β))
      rw [show β * (Real.pi / (2 * β)) = Real.pi / 2 from by field_simp,
        Real.sin_pi_div_two] at h
      norm_num at h
    have hα : α = 0 := by
      have h := (hcrit 1).1
      rw [(hcoeff 1).1, hβ, zero_mul, Real.cos_zero, Real.sin_zero] at h
      have hexp : Real.exp (α * 1) ^ 2 = 1 := by linarith
      have : Real.exp (α * 1) = 1 := by
        nlinarith [Real.exp_pos (α * 1), hexp]
      rw [Real.exp_eq_one_iff] at this
      linarith
    funext θ
    rw [hUf, hα, hβ, show zexp 0 0 θ = w1 from by simp [zexp], one_mul_W]
  · intro hUeq
    refine (preservesLeftQuadratic_iff (ζ := 1) (by norm_num) U).2 fun θ => ?_
    rw [hUeq]
    exact ⟨nRe_Uref θ, nSc_Uref θ⟩

/-! ## §25 — the `N₋` classification, run independently -/

/-- **`N₋` CONDITIONAL CLASSIFICATION (§25).**  The same classification holds for
the second branch.  The proof is *not* a renaming: it runs through the
branch-parameterized criterion, whose only branch input is the proved relation
`ζ * ζ = 1`, which both branches satisfy. -/
theorem Nminus_compatibility_classification {U : ℝ → W} (hU : IsContinuousFullLift U) :
    PreservesLeftQuadratic Nminus U ↔ U = Uref := by
  have hcrit : PreservesLeftQuadratic Nminus U ↔ ∀ θ, nRe (U θ) = 1 ∧ nSc (U θ) = 0 :=
    preservesLeftQuadratic_iff (ζ := -1) (by norm_num) U
  have hcritp : PreservesLeftQuadratic Nplus U ↔ ∀ θ, nRe (U θ) = 1 ∧ nSc (U θ) = 0 :=
    preservesLeftQuadratic_iff (ζ := 1) (by norm_num) U
  rw [hcrit, ← hcritp]
  exact Nplus_compatibility_classification hU

/-- **THE TWO CONDITIONAL CLASSES COINCIDE (§25).**  The two branch tests are
*equivalent*, for every map whatsoever: the difference between the branches is
invisible to this condition. -/
theorem Nplus_Nminus_compatibility_equiv (U : ℝ → W) :
    PreservesLeftQuadratic Nplus U ↔ PreservesLeftQuadratic Nminus U := by
  show PreservesLeftQuadratic (Ncand 1) U ↔ PreservesLeftQuadratic (Ncand (-1)) U
  rw [preservesLeftQuadratic_iff (ζ := 1) (by norm_num) U,
    preservesLeftQuadratic_iff (ζ := -1) (by norm_num) U]

/-! ## §26 — simultaneous compatibility -/

/-- **SIMULTANEOUS COMPATIBILITY IS NOT STRONGER (§26).**  Requiring both branch
tests removes nothing beyond either one of them. -/
theorem simultaneous_compatibility_classification {U : ℝ → W} (hU : IsContinuousFullLift U) :
    (PreservesLeftQuadratic Nplus U ∧ PreservesLeftQuadratic Nminus U) ↔ U = Uref := by
  constructor
  · rintro ⟨h, -⟩
    exact (Nplus_compatibility_classification hU).1 h
  · intro h
    exact ⟨(Nplus_compatibility_classification hU).2 h,
      (Nminus_compatibility_classification hU).2 h⟩

/-! ## §27 — normalization: assumed versus derived -/

/-- **NORMALIZATION DERIVED CONDITIONALLY (§27).**  No unit-norm condition was
assumed anywhere in Layers 1–7.  Under the *explicit* conditional test of §23 a
unit-like relation is now **derived**: the residual central factor of a
compatible continuous lift has unit squared modulus, and in fact equals the
unit. -/
theorem normalization_derived {U : ℝ → W} {α β : ℝ} (hU : ∀ θ, U θ = zexp α β θ ⋆ Uref θ)
    (hcont : IsContinuousFullLift U) (hpres : PreservesLeftQuadratic Nplus U) :
    (∀ θ, nRe (U θ) = 1 ∧ nSc (U θ) = 0) ∧
      (∀ θ, (Real.exp (α * θ) * Real.cos (β * θ)) ^ 2
        + (Real.exp (α * θ) * Real.sin (β * θ)) ^ 2 = 1) := by
  have hcrit := (preservesLeftQuadratic_iff (ζ := 1) (by norm_num) U).1 hpres
  refine ⟨hcrit, fun θ => ?_⟩
  have hUeq := (Nplus_compatibility_classification hcont).1 hpres
  have hparam : α = 0 ∧ β = 0 := by
    refine continuousFullLift_parameters_unique (α := α) (β := β) (α' := 0) (β' := 0) fun t => ?_
    rw [← hU t, hUeq, show zexp 0 0 t = w1 from by simp [zexp], one_mul_W]
  rw [hparam.1, hparam.2]
  simp

end NullSectorTask11
