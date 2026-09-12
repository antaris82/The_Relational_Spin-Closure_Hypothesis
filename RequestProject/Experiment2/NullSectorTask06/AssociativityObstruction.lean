import RequestProject.Experiment2.NullSectorTask06.GenericExtension

/-!
# Task 06, Phase B, Layer 1: the universal associativity question

Phase B starts again from an **arbitrary** bilinear product `M : BiProd4`
satisfying only `SectorCompatible M`.  No isotropy, no commutativity, no
orientation, no Phase-A classification and no specific alternating witness is
assumed; this module does not import `Task06.Rigidity`, `Task06.Existence`,
`Task06.ExactClassification`, `Task06.OrientationReversal`,
`Task06.Identification` or `Task06.Task04Comparison`.

The question settled here is existential:

```
does there exist M with SectorCompatible M ∧ Associative4 M ?
```

The answer is **no**, and the obstruction is exhibited in the smallest
configuration we could find: two orthonormal rest directions.
-/

namespace NullSectorTask06

open NullSectorTask01 NullSectorTask04

/-! ## The minimal algebraic obstruction -/

/-- **MINIMAL OBSTRUCTION, part 1.**  Purely formal consequence of a unit, two
anticommuting square roots of the unit, and associativity: their product squares
to minus the unit.  Only the listed identities are used — no sector
compatibility, no positivity, no coordinates. -/
theorem square_of_anticommuting_units {M : BiProd4} (hassoc : Associative4 M)
    (hu : ∀ X, M X e₀ = X) {a b : Vec4}
    (haa : M a a = e₀) (hbb : M b b = e₀) (hab : M b a = - M a b) :
    M (M a b) (M a b) = - e₀ := by
  have h1 : M (M a b) b = a := by rw [hassoc a b b, hbb, hu]
  have h2 : M b (M a b) = - a := by
    rw [← hassoc b a b, hab]
    simp only [map_neg, LinearMap.neg_apply, h1]
  rw [hassoc a b (M a b), h2]
  simp only [map_neg, haa]

/-- **MINIMAL OBSTRUCTION, part 2.**  For *every* sector-compatible product the
`e₀`-component of a square is a sum of squares, hence nonnegative.  This is the
only place where sector compatibility enters. -/
theorem sq_time_component {M : BiProd4} (hM : SectorCompatible M) (Z : Vec4) :
    (M Z Z).1 = Z.1 * Z.1 + dot3 Z.2 Z.2 := by
  have hexp := M_expand hM Z Z
  rw [M_rest_sq hM Z.2] at hexp
  have := congrArg (fun W : Vec4 => W.1) hexp
  simpa [e₀, sp] using this

theorem sq_time_component_nonneg {M : BiProd4} (hM : SectorCompatible M) (Z : Vec4) :
    0 ≤ (M Z Z).1 := by
  rw [sq_time_component hM]
  nlinarith [dot3_self_nonneg Z.2, sq_nonneg Z.1]

/-! ## The universal no-go theorem -/

/-- **UNIVERSAL OBSTRUCTION.**  No sector-compatible real bilinear product on
the `3+1` carrier is globally associative.  The statement quantifies over the
whole generic defect space: no isotropy, commutativity or orientation
assumption occurs. -/
theorem no_associative_sectorCompatible (M : BiProd4) (hM : SectorCompatible M) :
    ¬ Associative4 M := by
  intro hassoc
  -- two orthonormal rest directions, and the sector identities they inherit
  set a : Vec4 := sp r₁ with ha
  set b : Vec4 := sp r₂ with hb
  have haa : M a a = e₀ := by
    rw [ha, M_rest_sq hM r₁]
    norm_num [s₁]
  have hbb : M b b = e₀ := by
    rw [hb, M_rest_sq hM r₂]
    norm_num [s₂]
  have hsum : M a b + M b a = 0 := by
    rw [ha, hb, M_rest_symm hM r₁ r₂]
    norm_num [s₁, s₂]
  have hab : M b a = - M a b := by
    have := hsum
    linear_combination (norm := abel) this
  -- the product of the two directions squares to minus the unit
  have hkey := square_of_anticommuting_units hassoc (M_unit_right hM) haa hbb hab
  -- but every square has a nonnegative time component
  have hpos := sq_time_component_nonneg hM (M a b)
  rw [hkey] at hpos
  simp only [Prod.fst_neg, e₀_fst] at hpos
  linarith

/-- **UNIVERSAL OBSTRUCTION (existential form).** -/
theorem not_exists_associative_sectorCompatible :
    ¬ ∃ M : BiProd4, SectorCompatible M ∧ Associative4 M := by
  rintro ⟨M, hM, hassoc⟩
  exact no_associative_sectorCompatible M hM hassoc

/-- **The exact incompatible equations.**  For any sector-compatible `M`, write
`p = M (sp r₁) (sp r₂)` and split `p = τ • e₀ + sp u`.  Associativity forces
`p ⋆ p = -e₀`, while sector compatibility forces the `e₀`-component of `p ⋆ p`
to be `τ² + |u|²`.  The incompatible pair of equations is therefore

```
τ ^ 2 + dot3 u u = -1     with     0 ≤ τ ^ 2 + dot3 u u.
```
-/
theorem associativity_incompatible_equations {M : BiProd4} (hM : SectorCompatible M)
    (hassoc : Associative4 M) :
    (M (sp r₁) (sp r₂)).1 ^ 2 + dot3 (M (sp r₁) (sp r₂)).2 (M (sp r₁) (sp r₂)).2 = -1 := by
  have haa : M (sp r₁) (sp r₁) = e₀ := by rw [M_rest_sq hM r₁]; norm_num [s₁]
  have hbb : M (sp r₂) (sp r₂) = e₀ := by rw [M_rest_sq hM r₂]; norm_num [s₂]
  have hsum : M (sp r₁) (sp r₂) + M (sp r₂) (sp r₁) = 0 := by
    rw [M_rest_symm hM r₁ r₂]; norm_num [s₁, s₂]
  have hab : M (sp r₂) (sp r₁) = - M (sp r₁) (sp r₂) := by
    linear_combination (norm := abel) hsum
  have hkey := square_of_anticommuting_units hassoc (M_unit_right hM) haa hbb hab
  have hcomp := sq_time_component hM (M (sp r₁) (sp r₂))
  rw [hkey] at hcomp
  have h1 : ((-e₀ : Vec4)).1 = -1 := by simp [e₀]
  rw [h1] at hcomp
  nlinarith [hcomp]

end NullSectorTask06
