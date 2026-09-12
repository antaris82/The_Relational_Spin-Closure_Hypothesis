import RequestProject.Experiment2.NullSectorTask13.ReferenceSectorAction
import RequestProject.Experiment2.NullSectorTask11.InfinitesimalLift

/-!
# Task 13, Layer 6: the full Task-11 lift family restricted to an arbitrary carrier
(§19, §20, §21, §40)

The reference implementer is **not** silently substituted for the whole inherited family
(§19).  Everything below is stated for an arbitrary full lift `U` in the Task-11 sense —
in particular the residual central factor is kept, and neither `α = 0` nor `β = 0` is
imposed anywhere (§27).

## Results

* `rhoFull` and `full_lift_restriction_report` (§20) — well-definedness, identity at zero,
  the group law and invertibility on an arbitrary minimal carrier;
* `fullLift_preserves_slices` (§20) — every full lift preserves **both** slices, with
  equality of images; this needs neither continuity nor any normalization;
* `full_lift_action_plus_exact`, `full_lift_action_minus_exact` (§21) — the exact central
  factors, derived from `U = (central residual) ⋆ Uref` and the reference-sector theorem,
  never inserted by hand;
* `fullLift_central_compatibility` (§40) — the restricted action commutes with the
  internal central endomorphism algebra.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-! ## §20 — the restricted action of an arbitrary full lift -/

/-- **§20.  NEUTRAL DEFINITION.**  Left multiplication by an arbitrary full lift,
restricted to a left carrier. -/
noncomputable def rhoFull {L : Submodule ℝ W} (hL : IsLeftCarrier L) (U : ℝ → W)
    (θ : ℝ) : L →ₗ[ℝ] L where
  toFun ψ := ⟨U θ ⋆ (ψ : W), hL _ _ ψ.2⟩
  map_add' := by intro ψ φ; apply Subtype.ext; exact mul_add_W _ (ψ : W) (φ : W)
  map_smul' := by intro c ψ; apply Subtype.ext; exact mul_smul_W c _ (ψ : W)

@[simp] theorem rhoFull_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (U : ℝ → W)
    (θ : ℝ) (ψ : L) : ((rhoFull hL U θ ψ : L) : W) = U θ ⋆ (ψ : W) := rfl

theorem rhoFull_zero {L : Submodule ℝ W} (hL : IsLeftCarrier L) {U : ℝ → W}
    (hU : IsFullLift U) : rhoFull hL U 0 = LinearMap.id := by
  apply LinearMap.ext; intro ψ
  apply Subtype.ext
  simp only [rhoFull_coe, LinearMap.id_coe, id_eq]
  rw [hU.unit, one_mul_W]

theorem rhoFull_add {L : Submodule ℝ W} (hL : IsLeftCarrier L) {U : ℝ → W}
    (hU : IsFullLift U) (θ φ : ℝ) :
    rhoFull hL U (θ + φ) = (rhoFull hL U θ).comp (rhoFull hL U φ) := by
  apply LinearMap.ext; intro ψ
  apply Subtype.ext
  simp only [rhoFull_coe, LinearMap.comp_apply]
  rw [hU.group, mul_assoc_W]

theorem rhoFull_bijective {L : Submodule ℝ W} (hL : IsLeftCarrier L) {U : ℝ → W}
    (hU : IsFullLift U) (θ : ℝ) : Function.Bijective (rhoFull hL U θ) := by
  have hcomp : ∀ a b : ℝ, a + b = 0 →
      (rhoFull hL U a).comp (rhoFull hL U b) = LinearMap.id := by
    intro a b hab
    rw [← rhoFull_add hL hU, hab, rhoFull_zero hL hU]
  constructor
  · intro ψ φ h
    have h1 := congrArg (rhoFull hL U (-θ)) h
    have h2 := hcomp (-θ) θ (by ring)
    rw [show rhoFull hL U (-θ) (rhoFull hL U θ ψ)
        = (rhoFull hL U (-θ)).comp (rhoFull hL U θ) ψ from rfl,
      show rhoFull hL U (-θ) (rhoFull hL U θ φ)
        = (rhoFull hL U (-θ)).comp (rhoFull hL U θ) φ from rfl, h2] at h1
    simpa using h1
  · intro ψ
    refine ⟨rhoFull hL U (-θ) ψ, ?_⟩
    have := congrArg (fun T : L →ₗ[ℝ] L => T ψ) (hcomp θ (-θ) (by ring))
    simpa using this

/-! ## §20, §21 — the residual central factor and the exact sector actions -/

/-- **DERIVED (§21).**  Every full lift is the reference lift multiplied by a central
residual; this is the inherited Task-11 classification, recorded here in the form used
below. -/
theorem fullLift_central_residual {U : ℝ → W} (hU : IsFullLift U) :
    ∃ z : ℝ → W, IsCentralHom z ∧ ∀ θ, U θ = z θ ⋆ Uref θ :=
  (fullLift_classification U).1 hU

/-- **DERIVED.**  The values of a central residual lie in the inherited central plane. -/
theorem centralHom_mem_Z {z : ℝ → W} (hz : IsCentralHom z) (θ : ℝ) : z θ ∈ Z := by
  have h := hz.mem θ
  rwa [center_eq_Z] at h

/-- **PRINCIPAL THEOREM (§21): `full_lift_action_plus_exact`.**  For an arbitrary full
lift with central residual `z`, the action on the plus sector is by the central factor
`z θ ⋆ c₊^ref(θ)`.  The formula is *derived* from the residual decomposition and the
reference-sector theorem. -/
theorem full_lift_action_plus_exact {U z : ℝ → W} (hz : ∀ θ, U θ = z θ ⋆ Uref θ)
    {ψ : W} (hψ : ψ ∈ Hplus) (θ : ℝ) : U θ ⋆ ψ = (z θ ⋆ cPlusRef θ) ⋆ ψ := by
  rw [hz, mul_assoc_W, reference_action_plus_exact hψ, ← mul_assoc_W]

/-- **PRINCIPAL THEOREM (§21): `full_lift_action_minus_exact`. -/
theorem full_lift_action_minus_exact {U z : ℝ → W} (hz : ∀ θ, U θ = z θ ⋆ Uref θ)
    {ψ : W} (hψ : ψ ∈ Hminus) (θ : ℝ) : U θ ⋆ ψ = (z θ ⋆ cMinusRef θ) ⋆ ψ := by
  rw [hz, mul_assoc_W, reference_action_minus_exact hψ, ← mul_assoc_W]

/-- **PRINCIPAL THEOREM (§20).**  Every full lift preserves both slices of every left
carrier, with equality of images.  No continuity and no normalization is used. -/
theorem fullLift_preserves_slices {L : Submodule ℝ W} (hL : IsLeftCarrier L) {U : ℝ → W}
    (hU : IsFullLift U) (θ : ℝ) :
    Submodule.map (Lmul (U θ)) (Kplus L) = Kplus L ∧
    Submodule.map (Lmul (U θ)) (Kminus L) = Kminus L := by
  obtain ⟨z, hzhom, hz⟩ := fullLift_central_residual hU
  have hzZ : ∀ θ, z θ ∈ Z := fun θ => centralHom_mem_Z hzhom θ
  have hmemP : ∀ φ : W, φ ∈ Kplus L → U θ ⋆ φ ∈ Kplus L := by
    intro φ hφ
    rw [full_lift_action_plus_exact hz hφ.2]
    exact Kplus_central_stable hL (Z_mul_mem (hzZ θ) (cPlusRef_mem_Z θ)) hφ
  have hmemM : ∀ φ : W, φ ∈ Kminus L → U θ ⋆ φ ∈ Kminus L := by
    intro φ hφ
    rw [full_lift_action_minus_exact hz hφ.2]
    exact Kminus_central_stable hL (Z_mul_mem (hzZ θ) (cMinusRef_mem_Z θ)) hφ
  constructor
  · ext φ
    simp only [Submodule.mem_map, Lmul_apply]
    refine ⟨?_, fun hφ => ⟨U (-θ) ⋆ φ, ?_, ?_⟩⟩
    · rintro ⟨χ, hχ, rfl⟩; exact hmemP χ hχ
    · have : U (-θ) ⋆ φ ∈ Kplus L := by
        rw [full_lift_action_plus_exact hz hφ.2]
        exact Kplus_central_stable hL (Z_mul_mem (hzZ (-θ)) (cPlusRef_mem_Z (-θ))) hφ
      exact this
    · rw [← mul_assoc_W, hU.mul_neg, one_mul_W]
  · ext φ
    simp only [Submodule.mem_map, Lmul_apply]
    refine ⟨?_, fun hφ => ⟨U (-θ) ⋆ φ, ?_, ?_⟩⟩
    · rintro ⟨χ, hχ, rfl⟩; exact hmemM χ hχ
    · have : U (-θ) ⋆ φ ∈ Kminus L := by
        rw [full_lift_action_minus_exact hz hφ.2]
        exact Kminus_central_stable hL (Z_mul_mem (hzZ (-θ)) (cMinusRef_mem_Z (-θ))) hφ
      exact this
    · rw [← mul_assoc_W, hU.mul_neg, one_mul_W]

/-- **§20 SUMMARY.**  The complete list of §20 obligations for an arbitrary full lift and
an arbitrary minimal carrier. -/
theorem full_lift_restriction_report {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {U : ℝ → W} (hU : IsFullLift U) :
    (∀ (θ : ℝ) (ψ : W), ψ ∈ L → U θ ⋆ ψ ∈ L) ∧
    rhoFull hL.1.1 U 0 = LinearMap.id ∧
    (∀ θ φ : ℝ, rhoFull hL.1.1 U (θ + φ)
      = (rhoFull hL.1.1 U θ).comp (rhoFull hL.1.1 U φ)) ∧
    (∀ θ : ℝ, Function.Bijective (rhoFull hL.1.1 U θ)) ∧
    (∀ θ : ℝ, Submodule.map (Lmul (U θ)) (Kplus L) = Kplus L) ∧
    (∀ θ : ℝ, Submodule.map (Lmul (U θ)) (Kminus L) = Kminus L) :=
  ⟨fun _ _ hψ => hL.1.1 _ _ hψ, rhoFull_zero hL.1.1 hU, rhoFull_add hL.1.1 hU,
    rhoFull_bijective hL.1.1 hU,
    fun θ => (fullLift_preserves_slices hL.1.1 hU θ).1,
    fun θ => (fullLift_preserves_slices hL.1.1 hU θ).2⟩

/-! ## §21 — the exact factors of the continuous family, in closed form -/

/-- **DERIVED (§21).**  The exact central factor of the continuous full lift with
parameters `(α, β)` on the plus slice. -/
noncomputable def cPlusFull (α β θ : ℝ) : W :=
  zz (Real.exp (α * θ) * Real.cos (β * θ - θ / 2))
    (Real.exp (α * θ) * Real.sin (β * θ - θ / 2))

/-- **DERIVED (§21).**  The exact central factor on the minus slice. -/
noncomputable def cMinusFull (α β θ : ℝ) : W :=
  zz (Real.exp (α * θ) * Real.cos (β * θ + θ / 2))
    (Real.exp (α * θ) * Real.sin (β * θ + θ / 2))

theorem cPlusFull_mem_Z (α β θ : ℝ) : cPlusFull α β θ ∈ Z := zz_mem_Z _ _

theorem cMinusFull_mem_Z (α β θ : ℝ) : cMinusFull α β θ ∈ Z := zz_mem_Z _ _

theorem zexp_eq_zz (α β θ : ℝ) :
    zexp α β θ = zz (Real.exp (α * θ) * Real.cos (β * θ))
      (Real.exp (α * θ) * Real.sin (β * θ)) := rfl

/-- **DERIVED (§21).**  The closed form of the plus factor: the residual times the
reference factor. -/
theorem zexp_mul_cPlusRef (α β θ : ℝ) :
    zexp α β θ ⋆ cPlusRef θ = cPlusFull α β θ := by
  rw [zexp_eq_zz, cPlusRef, zz_mul_zz, cPlusFull,
    Real.cos_sub, Real.sin_sub]
  congr 1 <;> ring

/-- **DERIVED (§21).**  The closed form of the minus factor. -/
theorem zexp_mul_cMinusRef (α β θ : ℝ) :
    zexp α β θ ⋆ cMinusRef θ = cMinusFull α β θ := by
  rw [zexp_eq_zz, cMinusRef, zz_mul_zz, cMinusFull,
    Real.cos_add, Real.sin_add]
  congr 1 <;> ring

/-- **PRINCIPAL THEOREM (§21), closed form.**  For the continuous full lift with
parameters `(α, β)` the exact central factors on the two slices of an arbitrary minimal
carrier are `c₊(α,β,θ)` and `c₋(α,β,θ)`.  Neither `α = 0` nor `β = 0` is imposed. -/
theorem continuous_full_lift_sector_factors {U : ℝ → W} {α β : ℝ}
    (hU : ∀ θ, U θ = zexp α β θ ⋆ Uref θ) (θ : ℝ) :
    (∀ ψ ∈ Hplus, U θ ⋆ ψ = cPlusFull α β θ ⋆ ψ) ∧
    (∀ ψ ∈ Hminus, U θ ⋆ ψ = cMinusFull α β θ ⋆ ψ) := by
  constructor
  · intro ψ hψ
    rw [full_lift_action_plus_exact hU hψ, zexp_mul_cPlusRef]
  · intro ψ hψ
    rw [full_lift_action_minus_exact hU hψ, zexp_mul_cMinusRef]

/-! ## §40 — compatibility with the internal central endomorphisms -/

/-- **PRINCIPAL THEOREM (§40).**  The restricted axial action commutes with the internal
endomorphism algebra of the carrier: for every central `z` and every carrier element,
`U θ ⋆ (z ⋆ ψ) = z ⋆ (U θ ⋆ ψ)`.  This is proved from the centrality of `Z`, not inferred
from any scalar picture. -/
theorem fullLift_central_compatibility {U : ℝ → W} (_hU : IsFullLift U) {z : W}
    (hz : z ∈ Z) (θ : ℝ) (ψ : W) : U θ ⋆ (z ⋆ ψ) = z ⋆ (U θ ⋆ ψ) := by
  rw [← mul_assoc_W, ← Z_central hz (U θ), mul_assoc_W]

end NullSectorTask13
