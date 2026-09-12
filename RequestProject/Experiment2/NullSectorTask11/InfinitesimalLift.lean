import RequestProject.Experiment2.NullSectorTask11.QuadraticCompatibility

/-!
# Task 11, Layer 9: differentiable lifts and their infinitesimal generator (§28)

This layer is a **corollary layer**: the classification theorems of Layers 1–7
were proved under continuity alone, exactly as demanded by §8.  Only now is the
stronger differentiability hypothesis considered.

The outcome is that differentiability is not an extra restriction at all: every
continuous full lift is already differentiable, and its left generator

```
G := (d/dθ) U θ |_{θ = 0}
```

is computed exactly.  `G` is a purely algebraic object of the carrier; it is not
given any dynamical name.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## Expansion of the classified lift in the derived basis -/

/-- The product of a central-plane element with an element of the Task-10
two-plane, expanded in the derived basis.  Uses only the inherited
multiplication table (`wS ⋆ wR = -wA`). -/
theorem zc_mul_ksc_basis (a b c d : ℝ) :
    zc a b ⋆ ksc c d = (a * c) • w1 + (-(b * d)) • wA + (a * d) • wR + (b * c) • wS := by
  simp only [zc, ksc, add_mul_W, mul_add_W, smul_mul_W, mul_smul_W, one_mul_W,
    mul_one_W, wit8_wS_wR]
  module

/-- **DERIVED.**  The completely classified continuous full lift, expanded in the
derived basis.  Only four of the eight derived coordinates are occupied. -/
theorem fullLift_expand (α β θ : ℝ) :
    zexp α β θ ⋆ Uref θ =
      (Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) • w1
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) • wA
      + (-(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2))) • wR
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) • wS := by
  rw [zexp, Uref_apply, zc_mul_ksc_basis]
  module

/-! ## Elementary real derivatives used below -/

private theorem hasDerivAt_expc (α : ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (α * t)) (Real.exp (α * θ) * α) θ := by
  have h : HasDerivAt (fun t : ℝ => α * t) α θ := by
    simpa using (hasDerivAt_id θ).const_mul α
  simpa using h.exp

private theorem hasDerivAt_cosc (β : ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (β * t)) (-Real.sin (β * θ) * β) θ := by
  have h : HasDerivAt (fun t : ℝ => β * t) β θ := by
    simpa using (hasDerivAt_id θ).const_mul β
  simpa using h.cos

private theorem hasDerivAt_sinc (β : ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (β * t)) (Real.cos (β * θ) * β) θ := by
  have h : HasDerivAt (fun t : ℝ => β * t) β θ := by
    simpa using (hasDerivAt_id θ).const_mul β
  simpa using h.sin

private theorem hasDerivAt_cosh2 (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (t / 2)) (-Real.sin (θ / 2) * (1 / 2)) θ := by
  have h : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id θ).div_const 2
  simpa using h.cos

private theorem hasDerivAt_sinh2 (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (Real.cos (θ / 2) * (1 / 2)) θ := by
  have h : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id θ).div_const 2
  simpa using h.sin

/-! ## Differentiability of every continuous full lift -/

/-- **DERIVED.**  Every classified lift is differentiable; differentiability is
therefore *not* an additional restriction beyond continuity. -/
theorem differentiable_zexp_mul_Uref (α β : ℝ) :
    Differentiable ℝ fun θ => zexp α β θ ⋆ Uref θ := by
  have h : (fun θ => zexp α β θ ⋆ Uref θ) = fun θ : ℝ =>
      (Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) • w1
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) • wA
      + (-(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2))) • wR
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) • wS := by
    funext θ; exact fullLift_expand α β θ
  rw [h]
  intro θ
  exact ((((((hasDerivAt_expc α θ).mul (hasDerivAt_cosc β θ)).mul
      (hasDerivAt_cosh2 θ)).smul_const w1).add
      (((((hasDerivAt_expc α θ).mul (hasDerivAt_sinc β θ)).mul
        (hasDerivAt_sinh2 θ)).smul_const wA))).add
      ((((((hasDerivAt_expc α θ).mul (hasDerivAt_cosc β θ)).mul
        (hasDerivAt_sinh2 θ)).neg).smul_const wR))).add
      (((((hasDerivAt_expc α θ).mul (hasDerivAt_sinc β θ)).mul
        (hasDerivAt_cosh2 θ)).smul_const wS)) |>.differentiableAt

/-- **THE EXACT LEFT GENERATOR (§28).**  The derivative of the classified lift at
`θ = 0`. -/
theorem hasDerivAt_fullLift_zero (α β : ℝ) :
    HasDerivAt (fun θ => zexp α β θ ⋆ Uref θ)
      (zc α β - (2⁻¹ : ℝ) • wR) 0 := by
  have h : (fun θ => zexp α β θ ⋆ Uref θ) = fun θ : ℝ =>
      (Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) • w1
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) • wA
      + (-(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2))) • wR
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) • wS := by
    funext θ; exact fullLift_expand α β θ
  rw [h]
  have d0 : HasDerivAt
      (fun θ : ℝ => Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) α 0 := by
    simpa using ((hasDerivAt_expc α 0).mul (hasDerivAt_cosc β 0)).mul (hasDerivAt_cosh2 0)
  have d1 : HasDerivAt
      (fun θ : ℝ => Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) 0 0 := by
    simpa using ((hasDerivAt_expc α 0).mul (hasDerivAt_sinc β 0)).mul (hasDerivAt_sinh2 0)
  have d6 : HasDerivAt
      (fun θ : ℝ => -(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2)))
      (-(2⁻¹ : ℝ)) 0 := by
    have := (((hasDerivAt_expc α 0).mul (hasDerivAt_cosc β 0)).mul (hasDerivAt_sinh2 0)).neg
    norm_num at this ⊢
    exact this
  have d7 : HasDerivAt
      (fun θ : ℝ => Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) β 0 := by
    simpa using ((hasDerivAt_expc α 0).mul (hasDerivAt_sinc β 0)).mul (hasDerivAt_cosh2 0)
  have hd := (((d0.smul_const w1).add (d1.smul_const wA)).add
    (d6.smul_const wR)).add (d7.smul_const wS)
  convert hd using 1
  rw [zc]
  module

/-! ## §28 — differentiable full lifts -/

/-- **DIFFERENTIABLE FULL LIFT (§28).**  A full-carrier lift whose parameter
dependence is differentiable in the inherited finite-dimensional topology. -/
structure IsDifferentiableFullLift (U : ℝ → W) : Prop extends IsFullLift U where
  /-- Differentiability in the inherited topology. -/
  diff : Differentiable ℝ U

/-- A differentiable full lift is a continuous full lift. -/
theorem IsDifferentiableFullLift.toIsContinuousFullLift {U : ℝ → W}
    (hU : IsDifferentiableFullLift U) : IsContinuousFullLift U where
  toIsFullLift := hU.toIsFullLift
  cont := hU.diff.continuous

/-- **DERIVED (§28).**  Continuity and differentiability of a full lift are
*equivalent*: the continuous classification already produces differentiable
maps.  No new hypothesis is added by passing to the differentiable case. -/
theorem continuousFullLift_iff_differentiableFullLift (U : ℝ → W) :
    IsContinuousFullLift U ↔ IsDifferentiableFullLift U := by
  constructor
  · intro hU
    obtain ⟨α, β, hUf⟩ := (continuousFullLift_classification U).1 hU
    refine ⟨hU.toIsFullLift, ?_⟩
    have h : U = fun θ => zexp α β θ ⋆ Uref θ := funext hUf
    rw [h]
    exact differentiable_zexp_mul_Uref α β
  · exact fun hU => hU.toIsContinuousFullLift

/-- **LEFT GENERATOR (§28).**  The infinitesimal left generator of a
differentiable lift.  Neutral name: no dynamical interpretation is attached. -/
noncomputable def leftGen (U : ℝ → W) : W := deriv U 0

/-- **THE EXACT INFINITESIMAL GENERATOR OF AN ARBITRARY DIFFERENTIABLE LIFT
(§28).**  It consists of an arbitrary element of the inherited central plane
(the residual, invisible part) plus the *fixed* half-weighted axis element
`-(1/2)·R` (the visible part). -/
theorem differentiableFullLift_generator {U : ℝ → W} (hU : IsDifferentiableFullLift U) :
    ∃ α β : ℝ, (∀ θ, U θ = zexp α β θ ⋆ Uref θ) ∧
      leftGen U = zc α β - (2⁻¹ : ℝ) • wR := by
  obtain ⟨α, β, hUf⟩ := (continuousFullLift_classification U).1 hU.toIsContinuousFullLift
  refine ⟨α, β, hUf, ?_⟩
  have h : U = fun θ => zexp α β θ ⋆ Uref θ := funext hUf
  rw [leftGen, h]
  exact (hasDerivAt_fullLift_zero α β).deriv

/-- **EVERY SUCH GENERATOR OCCURS (§28).**  The set of infinitesimal left
generators of differentiable full lifts is exactly the affine two-plane
`Z - (1/2)·R`. -/
theorem generator_exists (α β : ℝ) :
    ∃ U : ℝ → W, IsDifferentiableFullLift U ∧ leftGen U = zc α β - (2⁻¹ : ℝ) • wR := by
  refine ⟨fun θ => zexp α β θ ⋆ Uref θ, ?_, (hasDerivAt_fullLift_zero α β).deriv⟩
  refine (continuousFullLift_iff_differentiableFullLift _).1 ?_
  exact (continuousFullLift_classification _).2 ⟨α, β, fun _ => rfl⟩

/-- **EXACT GENERATOR CLASSIFICATION (§28).**  A carrier element is the
infinitesimal left generator of some differentiable full lift **iff** it differs
from `-(1/2)·R` by an element of the inherited central plane. -/
theorem generator_classification (G : W) :
    (∃ U : ℝ → W, IsDifferentiableFullLift U ∧ leftGen U = G) ↔
      G + (2⁻¹ : ℝ) • wR ∈ Z := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨α, β, -, hG⟩ := differentiableFullLift_generator hU
    rw [hG]
    have : zc α β - (2⁻¹ : ℝ) • wR + (2⁻¹ : ℝ) • wR = zc α β := by module
    rw [this]
    exact zc_mem_Z α β
  · intro hG
    obtain ⟨α, β, hab⟩ := (mem_Z_iff _).1 hG
    obtain ⟨U, hU, hUG⟩ := generator_exists α β
    refine ⟨U, hU, ?_⟩
    rw [hUG]
    have : G = α • w1 + β • wS - (2⁻¹ : ℝ) • wR := by
      have := hab
      rw [show G = (G + (2⁻¹ : ℝ) • wR) - (2⁻¹ : ℝ) • wR from by module, this]
    rw [this, zc]

end NullSectorTask11
