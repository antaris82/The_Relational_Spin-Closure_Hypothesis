import RequestProject.Experiment2.NullSectorTask13.SliceCentralStructure
import RequestProject.Experiment2.NullSectorTask11.ReferenceExistence

/-!
# Task 13, Layer 4: the reference lift restricted to an arbitrary carrier (§12, §13)

**Source order (§12, §46).**  This is the first Task-13 module in which the inherited
reference implementer `Uref` appears.  The arbitrary minimal carrier `L` and its two
axis-relative slices were defined before it, without using any property of `Uref`, and in
particular without its explicit coefficient formula.

Here only the *structural* consequences of the inherited facts

* `Uref 0 = 1`,
* `Uref (θ + φ) = Uref θ ⋆ Uref φ`,
* `Uref` implements the inherited automorphism family by conjugation

are used.  The explicit coefficients enter first in the next module, and there only to
*derive* the sector actions — never to define them (§12).

Nothing here is called a representation.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-! ## §13 — the restricted reference action -/

/-- **§13.  NEUTRAL DEFINITION.**  Left multiplication by the reference implementer,
restricted to a left carrier.  Well-definedness is exactly left stability. -/
noncomputable def rhoRef {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    L →ₗ[ℝ] L where
  toFun ψ := ⟨Uref θ ⋆ (ψ : W), hL _ _ ψ.2⟩
  map_add' := by intro ψ φ; apply Subtype.ext; exact mul_add_W _ (ψ : W) (φ : W)
  map_smul' := by intro c ψ; apply Subtype.ext; exact mul_smul_W c _ (ψ : W)

@[simp] theorem rhoRef_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) (ψ : L) :
    ((rhoRef hL θ ψ : L) : W) = Uref θ ⋆ (ψ : W) := rfl

/-- **DERIVED (§13.1).**  Well-definedness, stated at the level of the carrier. -/
theorem rhoRef_mem {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) {ψ : W}
    (hψ : ψ ∈ L) : Uref θ ⋆ ψ ∈ L := hL _ _ hψ

/-- **DERIVED (§13.4).**  Identity at the parameter value zero. -/
theorem rhoRef_zero {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    rhoRef hL 0 = LinearMap.id := by
  apply LinearMap.ext; intro ψ
  apply Subtype.ext
  simp only [rhoRef_coe, LinearMap.id_coe, id_eq]
  rw [Uref_isFullLift.unit, one_mul_W]

/-- **DERIVED (§13.5).**  The one-parameter group law. -/
theorem rhoRef_add {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ φ : ℝ) :
    rhoRef hL (θ + φ) = (rhoRef hL θ).comp (rhoRef hL φ) := by
  apply LinearMap.ext; intro ψ
  apply Subtype.ext
  simp only [rhoRef_coe, LinearMap.comp_apply]
  rw [Uref_isFullLift.group, mul_assoc_W]

/-- **DERIVED (§13.3).**  Invertibility, with the explicit inverse at the opposite
parameter value. -/
theorem rhoRef_comp_neg {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    (rhoRef hL θ).comp (rhoRef hL (-θ)) = LinearMap.id := by
  rw [← rhoRef_add, add_neg_cancel, rhoRef_zero]

theorem rhoRef_neg_comp {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    (rhoRef hL (-θ)).comp (rhoRef hL θ) = LinearMap.id := by
  rw [← rhoRef_add, neg_add_cancel, rhoRef_zero]

/-- **DERIVED (§13.3).**  The restricted reference action is bijective. -/
theorem rhoRef_bijective {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    Function.Bijective (rhoRef hL θ) := by
  constructor
  · intro ψ φ h
    have h1 := congrArg (rhoRef hL (-θ)) h
    rw [show rhoRef hL (-θ) (rhoRef hL θ ψ) = (rhoRef hL (-θ)).comp (rhoRef hL θ) ψ from rfl,
      show rhoRef hL (-θ) (rhoRef hL θ φ) = (rhoRef hL (-θ)).comp (rhoRef hL θ) φ from rfl,
      rhoRef_neg_comp] at h1
    simpa using h1
  · intro ψ
    refine ⟨rhoRef hL (-θ) ψ, ?_⟩
    have := congrArg (fun T : L →ₗ[ℝ] L => T ψ) (rhoRef_comp_neg hL θ)
    simpa using this

/-! ## §13.6 — continuity in the parameter -/

/-- **DERIVED (§13.6).**  For each carrier element the restricted action is continuous in
the parameter, in the inherited finite-dimensional topology. -/
theorem rhoRef_continuous {L : Submodule ℝ W} (hL : IsLeftCarrier L) (ψ : L) :
    Continuous fun θ : ℝ => ((rhoRef hL θ ψ : L) : W) := by
  simp only [rhoRef_coe]
  refine continuous_pi fun i => ?_
  have hcont : Continuous fun θ : ℝ => Uref θ := Uref_continuous
  have : (fun θ : ℝ => (Uref θ ⋆ (ψ : W)) i)
      = fun θ : ℝ => wit8MulFun (Uref θ) (ψ : W) i := rfl
  rw [this]
  have h0 : Continuous fun θ : ℝ => Uref θ 0 := (continuous_apply 0).comp hcont
  have h1 : Continuous fun θ : ℝ => Uref θ 1 := (continuous_apply 1).comp hcont
  have h2 : Continuous fun θ : ℝ => Uref θ 2 := (continuous_apply 2).comp hcont
  have h3 : Continuous fun θ : ℝ => Uref θ 3 := (continuous_apply 3).comp hcont
  have h4 : Continuous fun θ : ℝ => Uref θ 4 := (continuous_apply 4).comp hcont
  have h5 : Continuous fun θ : ℝ => Uref θ 5 := (continuous_apply 5).comp hcont
  have h6 : Continuous fun θ : ℝ => Uref θ 6 := (continuous_apply 6).comp hcont
  have h7 : Continuous fun θ : ℝ => Uref θ 7 := (continuous_apply 7).comp hcont
  fin_cases i <;> simp only [wit8MulFun] <;> simp <;> fun_prop

/-! ## §13.7 — the exact behaviour at `2π` and `4π` -/

theorem Uref_two_pi' : Uref (2 * Real.pi) = -w1 := Ustd_two_pi

theorem Uref_four_pi' : Uref (4 * Real.pi) = w1 := Ustd_four_pi

/-- **PRINCIPAL THEOREM (§13.7), REFERENCE LIFT.**  On every left carrier the restricted
reference action at `2π` is minus the identity, and at `4π` it is the identity.  This is
an *internal carrier* statement; the inherited algebra automorphism is already the
identity at `2π`. -/
theorem rhoRef_two_pi_four_pi {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    rhoRef hL (2 * Real.pi) = -LinearMap.id ∧ rhoRef hL (4 * Real.pi) = LinearMap.id := by
  constructor
  · apply LinearMap.ext; intro ψ
    apply Subtype.ext
    simp only [rhoRef_coe, LinearMap.neg_apply, LinearMap.id_coe, id_eq]
    rw [Uref_two_pi']
    rw [show (-w1 : W) = (-1 : ℝ) • w1 from by module, smul_mul_W, one_mul_W]
    simp
  · apply LinearMap.ext; intro ψ
    apply Subtype.ext
    simp only [rhoRef_coe, LinearMap.id_coe, id_eq]
    rw [Uref_four_pi', one_mul_W]

/-- **§13 SUMMARY.**  The complete list of §13 obligations, for an arbitrary left carrier:
well-definedness, real linearity (the type of `rhoRef`), invertibility, identity at zero,
the group law, continuity, and the exact `2π` / `4π` behaviour. -/
theorem reference_restriction_report {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    (∀ (θ : ℝ) (ψ : W), ψ ∈ L → Uref θ ⋆ ψ ∈ L) ∧
    rhoRef hL 0 = LinearMap.id ∧
    (∀ θ φ : ℝ, rhoRef hL (θ + φ) = (rhoRef hL θ).comp (rhoRef hL φ)) ∧
    (∀ θ : ℝ, Function.Bijective (rhoRef hL θ)) ∧
    (∀ ψ : L, Continuous fun θ : ℝ => ((rhoRef hL θ ψ : L) : W)) ∧
    rhoRef hL (2 * Real.pi) = -LinearMap.id ∧
    rhoRef hL (4 * Real.pi) = LinearMap.id :=
  ⟨fun θ _ hψ => rhoRef_mem hL θ hψ, rhoRef_zero hL, rhoRef_add hL, rhoRef_bijective hL,
    rhoRef_continuous hL, (rhoRef_two_pi_four_pi hL).1, (rhoRef_two_pi_four_pi hL).2⟩

end NullSectorTask13
