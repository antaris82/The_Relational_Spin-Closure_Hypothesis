import RequestProject.Experiment2.NullSectorTask13.ReferenceRestriction

/-!
# Task 13, Layer 5: the exact reference action on the slices (§14–§18)

The two sector actions are **derived** here, from

* the inherited multiplication,
* the defining sector relations `R ⋆ ψ = ± S ⋆ ψ` of `H₊` and `H₋`,
* and the inherited fact that `Uref` implements the axial automorphism family,

and not transferred from the Task-10 statement about the provisional regular carrier
(§12, §15, §16).  The minus sector is treated independently of the plus sector: no sign
symmetry is invoked at prose level (§16).

## Results

* `reference_preserves_plus_slice`, `reference_preserves_minus_slice` (§14) — with
  equality of images, using invertibility;
* `reference_action_plus_exact` (§15) and `reference_action_minus_exact` (§16) — the exact
  central factors `c₊^ref(θ) = cos(θ/2) • 1 − sin(θ/2) • S` and
  `c₋^ref(θ) = cos(θ/2) • 1 + sin(θ/2) • S`;
* `reference_relative_action_exact` (§17) — the two factors are **mutually inverse**
  central units, and the division-free relative identity
  `c₊^ref(θ) = Rel(θ) ⋆ c₋^ref(θ)` holds with `Rel(θ) = cos θ • 1 − sin θ • S`;
* `reference_action_carrier_independent` (§18) — the factors do not depend on the carrier.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-! ## The two central factors -/

/-- **DERIVED (§15).**  The central factor of the reference action on the plus sector. -/
noncomputable def cPlusRef (θ : ℝ) : W := zz (Real.cos (θ / 2)) (-Real.sin (θ / 2))

/-- **DERIVED (§16).**  The central factor of the reference action on the minus
sector. -/
noncomputable def cMinusRef (θ : ℝ) : W := zz (Real.cos (θ / 2)) (Real.sin (θ / 2))

theorem cPlusRef_mem_Z (θ : ℝ) : cPlusRef θ ∈ Z := zz_mem_Z _ _

theorem cMinusRef_mem_Z (θ : ℝ) : cMinusRef θ ∈ Z := zz_mem_Z _ _

/-! ## §15 — the exact reference action on the plus sector -/

/-- **PRINCIPAL THEOREM (§15): `reference_action_plus_exact`.**  For every element of the
plus sector — in particular for every element of the plus slice of an arbitrary minimal
carrier — the reference implementer acts by the central factor
`cos(θ/2) • 1 − sin(θ/2) • S`.  The formula is derived from `R ⋆ ψ = S ⋆ ψ`; the Task-10
statement about the regular carrier is not used. -/
theorem reference_action_plus_exact {ψ : W} (hψ : ψ ∈ Hplus) (θ : ℝ) :
    Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ := by
  rw [Uref_apply, ksc_mul_left, cPlusRef, zz_mul, wR_mul_eq_wS_mul_of_mem_Hplus hψ]

/-- **PRINCIPAL THEOREM (§16): `reference_action_minus_exact`.**  Independent derivation
on the minus sector, from `R ⋆ ψ = -(S ⋆ ψ)`: the central factor is
`cos(θ/2) • 1 + sin(θ/2) • S`. -/
theorem reference_action_minus_exact {ψ : W} (hψ : ψ ∈ Hminus) (θ : ℝ) :
    Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ := by
  rw [Uref_apply, ksc_mul_left, cMinusRef, zz_mul, wR_mul_eq_neg_wS_mul_of_mem_Hminus hψ]
  module

/-! ## §14 — sector invariance -/

/-- **PRINCIPAL THEOREM (§14): `reference_preserves_plus_slice`.**  The restricted
reference action maps the plus slice of an arbitrary left carrier *onto* itself. -/
theorem reference_preserves_plus_slice {L : Submodule ℝ W} (hL : IsLeftCarrier L)
    (θ : ℝ) : Submodule.map (Lmul (Uref θ)) (Kplus L) = Kplus L := by
  ext φ
  simp only [Submodule.mem_map, Lmul_apply]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    rw [reference_action_plus_exact hψ.2]
    exact Kplus_central_stable hL (cPlusRef_mem_Z θ) hψ
  · intro hφ
    refine ⟨Uref (-θ) ⋆ φ, ?_, ?_⟩
    · rw [reference_action_plus_exact hφ.2]
      exact Kplus_central_stable hL (cPlusRef_mem_Z (-θ)) hφ
    · rw [← mul_assoc_W, Uref_isFullLift.mul_neg, one_mul_W]

/-- **PRINCIPAL THEOREM (§14): `reference_preserves_minus_slice`.**  Independently proved
for the minus slice. -/
theorem reference_preserves_minus_slice {L : Submodule ℝ W} (hL : IsLeftCarrier L)
    (θ : ℝ) : Submodule.map (Lmul (Uref θ)) (Kminus L) = Kminus L := by
  ext φ
  simp only [Submodule.mem_map, Lmul_apply]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    rw [reference_action_minus_exact hψ.2]
    exact Kminus_central_stable hL (cMinusRef_mem_Z θ) hψ
  · intro hφ
    refine ⟨Uref (-θ) ⋆ φ, ?_, ?_⟩
    · rw [reference_action_minus_exact hφ.2]
      exact Kminus_central_stable hL (cMinusRef_mem_Z (-θ)) hφ
    · rw [← mul_assoc_W, Uref_isFullLift.mul_neg, one_mul_W]

/-! ## §17 — the exact relation between the two sector actions -/

/-- **DERIVED (§17).**  The intrinsic relative factor of the reference action: the central
element at the *full* parameter value. -/
noncomputable def RelRef (θ : ℝ) : W := zz (Real.cos θ) (-Real.sin θ)

theorem RelRef_mem_Z (θ : ℝ) : RelRef θ ∈ Z := zz_mem_Z _ _

/-- **PRINCIPAL THEOREM (§17): `reference_relative_action_exact`.**  The two sector
factors are exactly mutually inverse central units; each is obtained from the other by
reversing the sign of the central generator; and the division-free relative identity
`c₊(θ) = Rel(θ) ⋆ c₋(θ)` holds with the relative factor `Rel(θ) = cos θ • 1 − sin θ • S`,
which is the *square* of the plus factor.  Only after this theorem is the descriptive
language "opposite sector factors" used in the report. -/
theorem reference_relative_action_exact (θ : ℝ) :
    cPlusRef θ ⋆ cMinusRef θ = w1 ∧
    cPlusRef θ = RelRef θ ⋆ cMinusRef θ ∧
    RelRef θ = cPlusRef θ ⋆ cPlusRef θ ∧
    cMinusRef θ ⋆ cPlusRef θ = w1 := by
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  have hc : Real.cos θ = Real.cos (θ / 2) * Real.cos (θ / 2)
      - Real.sin (θ / 2) * Real.sin (θ / 2) := by
    have := Real.cos_two_mul' (θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring] at this
    rw [this]; ring
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring] at this
    rw [this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cPlusRef, cMinusRef, zz_mul_zz]
    have h1 : Real.cos (θ / 2) * Real.cos (θ / 2)
        - -Real.sin (θ / 2) * Real.sin (θ / 2) = 1 := by nlinarith [hpy]
    have h2 : Real.cos (θ / 2) * Real.sin (θ / 2)
        + -Real.sin (θ / 2) * Real.cos (θ / 2) = 0 := by ring
    rw [h1, h2, zz_one_zero]
  · rw [cPlusRef, cMinusRef, RelRef, zz_mul_zz, hc, hs]
    congr 1
    · linear_combination (-(Real.cos (θ / 2))) * hpy
    · linear_combination Real.sin (θ / 2) * hpy
  · rw [cPlusRef, RelRef, zz_mul_zz, hc, hs]
    congr 1
    · ring
    · ring
  · rw [cPlusRef, cMinusRef, zz_mul_zz]
    have h1 : Real.cos (θ / 2) * Real.cos (θ / 2)
        - Real.sin (θ / 2) * -Real.sin (θ / 2) = 1 := by nlinarith [hpy]
    have h2 : Real.cos (θ / 2) * -Real.sin (θ / 2)
        + Real.sin (θ / 2) * Real.cos (θ / 2) = 0 := by ring
    rw [h1, h2, zz_one_zero]

/-- **DERIVED (§17).**  Both sector factors are one-parameter groups in the central
plane, and the relative factor is one as well. -/
theorem reference_sector_factors_group (θ φ : ℝ) :
    cPlusRef (θ + φ) = cPlusRef θ ⋆ cPlusRef φ ∧
    cMinusRef (θ + φ) = cMinusRef θ ⋆ cMinusRef φ ∧
    RelRef (θ + φ) = RelRef θ ⋆ RelRef φ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cPlusRef, cPlusRef, cPlusRef, zz_mul_zz,
      show (θ + φ) / 2 = θ / 2 + φ / 2 from by ring, Real.cos_add, Real.sin_add]
    congr 1 <;> ring
  · rw [cMinusRef, cMinusRef, cMinusRef, zz_mul_zz,
      show (θ + φ) / 2 = θ / 2 + φ / 2 from by ring, Real.cos_add, Real.sin_add]
    congr 1; ring
  · rw [RelRef, RelRef, RelRef, zz_mul_zz, Real.cos_add, Real.sin_add]
    congr 1 <;> ring

/-! ## §18 — carrier independence of the reference sector action -/

/-- **PRINCIPAL THEOREM (§18): `reference_action_carrier_independent`,
`CARRIER-INDEPENDENT`.**  The restricted reference action depends only on the
axis-relative sector of the element, never on the minimal carrier it is taken from: one
and the same pair of central factors governs the plus and the minus slice of *every*
minimal carrier. -/
theorem reference_action_carrier_independent
    {L L' : Submodule ℝ W} (_hL : IsMinimalLeftCarrier L) (_hL' : IsMinimalLeftCarrier L')
    (θ : ℝ) :
    (∀ ψ ∈ Kplus L, Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
    (∀ ψ ∈ Kplus L', Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
    (∀ ψ ∈ Kminus L, Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ) ∧
    (∀ ψ ∈ Kminus L', Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ) :=
  ⟨fun _ hψ => reference_action_plus_exact hψ.2 θ,
    fun _ hψ => reference_action_plus_exact hψ.2 θ,
    fun _ hψ => reference_action_minus_exact hψ.2 θ,
    fun _ hψ => reference_action_minus_exact hψ.2 θ⟩

/-! ## The restricted reference action on the slices, as endomorphisms -/

/-- **§14.**  The reference action restricted to the plus slice. -/
noncomputable def rhoRefP {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    Kplus L →ₗ[ℝ] Kplus L where
  toFun ψ := ⟨Uref θ ⋆ (ψ : W), by
    rw [reference_action_plus_exact (mem_Hplus_of_mem_Kplus ψ.2)]
    exact Kplus_central_stable hL (cPlusRef_mem_Z θ) ψ.2⟩
  map_add' := by intro ψ φ; apply Subtype.ext; exact mul_add_W _ (ψ : W) (φ : W)
  map_smul' := by intro c ψ; apply Subtype.ext; exact mul_smul_W c _ (ψ : W)

@[simp] theorem rhoRefP_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ)
    (ψ : Kplus L) : ((rhoRefP hL θ ψ : Kplus L) : W) = Uref θ ⋆ (ψ : W) := rfl

/-- **§14.**  The reference action restricted to the minus slice. -/
noncomputable def rhoRefM {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    Kminus L →ₗ[ℝ] Kminus L where
  toFun ψ := ⟨Uref θ ⋆ (ψ : W), by
    rw [reference_action_minus_exact (mem_Hminus_of_mem_Kminus ψ.2)]
    exact Kminus_central_stable hL (cMinusRef_mem_Z θ) ψ.2⟩
  map_add' := by intro ψ φ; apply Subtype.ext; exact mul_add_W _ (ψ : W) (φ : W)
  map_smul' := by intro c ψ; apply Subtype.ext; exact mul_smul_W c _ (ψ : W)

@[simp] theorem rhoRefM_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ)
    (ψ : Kminus L) : ((rhoRefM hL θ ψ : Kminus L) : W) = Uref θ ⋆ (ψ : W) := rfl

/-! ## §41 — the commutant of the restricted axial action on a slice -/

/-- **PRINCIPAL THEOREM (§41), second commutant.**  On a slice the reference action is
multiplication by a central element, so an endomorphism commutes with the *whole*
reference family exactly when it commutes with the central element `S`.  The two
commutants of §41 therefore coincide for the full one-parameter family — this is proved,
not assumed.  (For the exceptional parameter values `θ ∈ 2πℤ` the individual restricted
action is a real scalar and commutes with every endomorphism, so commutation at a single
parameter value is strictly weaker.) -/
theorem slice_plus_axial_commutant {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ : W} (hψ : ψ ∈ Kplus L) (hne : ψ ≠ 0) (T : Kplus L →ₗ[ℝ] Kplus L) :
    (∀ θ : ℝ, T.comp (rhoRefP hL.1.1 θ) = (rhoRefP hL.1.1 θ).comp T) ↔
      ∃ a b : ℝ, ∀ φ : Kplus L, ((T φ : Kplus L) : W) = zz a b ⋆ (φ : W) := by
  constructor
  · intro hT
    refine (slice_plus_central_commutant hL hψ hne T).1 ?_
    intro φ
    have h := congrArg (fun F : Kplus L →ₗ[ℝ] Kplus L => ((F φ : Kplus L) : W))
      (hT Real.pi)
    simp only [LinearMap.comp_apply, rhoRefP_coe] at h
    have hU : Uref Real.pi = -wR := by
      rw [Uref_apply]
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two, ksc]
      module
    rw [hU, neg_mul_W, wR_mul_eq_wS_mul_of_mem_Hplus (mem_Hplus_of_mem_Kplus (T φ).2)] at h
    have hφS : ((rhoRefP hL.1.1 Real.pi φ : Kplus L) : W) = -(wS ⋆ (φ : W)) := by
      rw [rhoRefP_coe, hU, neg_mul_W, wR_mul_eq_wS_mul_of_mem_Hplus (mem_Hplus_of_mem_Kplus φ.2)]
    have hEq : rhoRefP hL.1.1 Real.pi φ = -(SopP hL.1.1 φ) := by
      apply Subtype.ext; rw [hφS]; simp
    rw [hEq, map_neg] at h
    simp only [Submodule.coe_neg] at h
    have := congrArg (fun y : W => -y) h
    simpa using this
  · rintro ⟨a, b, hab⟩ θ
    apply LinearMap.ext; intro φ
    apply Subtype.ext
    simp only [LinearMap.comp_apply, rhoRefP_coe, hab]
    rw [← mul_assoc_W, ← mul_assoc_W, zz_central a b (Uref θ)]

end NullSectorTask13
