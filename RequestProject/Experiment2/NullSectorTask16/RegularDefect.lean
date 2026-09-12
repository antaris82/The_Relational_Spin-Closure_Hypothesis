import RequestProject.Experiment2.NullSectorTask16.TransformationValuedClosure

/-!
# Task 16, Layer 4 (Work Package 4): the central composition defect under joint regularity

Work Package 3 showed that exact transformation-valuedness is impossible for a jointly
regular family.  The strongest requirement that *does* survive is the sign-relaxed one:
equal visible transformations receive internal representatives that agree **up to a
central sign**.

This layer

* introduces that class intrinsically (`IsSignTransformationValued`) — no quotient is
  taken, the sign is carried explicitly as an element of the carrier;
* proves that the class is nonempty: the inherited reference family belongs to it
  (`reference_signTransformationValued`);
* proves that it is *exactly one* family: every jointly regular sign-valued family
  coincides with the inherited reference family on every unit direction
  (`signValued_eq_reference`);
* shows that the surviving defect on closed visible relations is exactly the two-element
  set `{1, -1}` inside the central units (`signValued_defect_pm_one`), and that both values
  really occur (`reference_sign_defect_nontrivial`);
* shows by an explicit witness that *without* the sign-valued normalization the coincidence
  defect is **not** discrete: it ranges over central units of arbitrary modulus
  (`defect_not_discrete_without_normalization`);
* records the finite consistency identities that follow from associativity alone
  (`defect_chain`, `defect_same_axis_trivial`).

The two sources of discrepancy are kept apart throughout: the inherited discrete
reference-word defect (which is what produces the `±1` above) and the continuous central
residual freedom (which is what the negative control exhibits).
-/

namespace NullSectorTask16

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15

/-! ## Bookkeeping for the central exponential–rotation family -/

theorem zexp_zero_eq (θ : ℝ) : zexp 0 0 θ = w1 := by
  simp [zexp]

theorem zexp_zero_add (b₁ b₂ θ : ℝ) :
    zexp 0 b₁ θ ⋆ zexp 0 b₂ θ = zexp 0 (b₁ + b₂) θ := by
  simp only [zexp, zc, zero_mul, Real.exp_zero, one_mul]
  rw [central_mul_rule]
  rw [show (b₁ + b₂) * θ = b₁ * θ + b₂ * θ by ring, Real.cos_add, Real.sin_add]
  congr 1
  ring

/-! ## The reference family -/

/-- **NEUTRAL DEFINITION.**  The inherited reference implementations, read as a family
indexed by direction and parameter. -/
noncomputable def refFam (n : Vec3) (θ : ℝ) : W := Un n θ

theorem refFam_eq_famOf : refFam = famOf (fun _ => 0) (fun _ => 0) := by
  funext n θ
  rw [refFam, famOf, zexp_zero_eq, one_mul_W]

/-- **DERIVED.**  The inherited reference family is jointly regular. -/
theorem refFam_jointlyRegular : IsJointlyRegularFamily refFam := by
  rw [refFam_eq_famOf]
  exact jointlyRegular_famOf continuous_const continuous_const

/-! ## Work Package 4 — the surviving class -/

/-- **NEUTRAL DEFINITION (Work Package 4).**  A family is *sign-transformation-valued* when
equal inherited visible automorphisms receive internal representatives that agree up to the
central sign.  The sign is carried explicitly; nothing is quotiented. -/
def IsSignTransformationValued (U : Vec3 → ℝ → W) : Prop :=
  ∀ (n m : Vec3) (θ φ : ℝ), IsUnitAxis n → IsUnitAxis m →
    PhiGen n θ = PhiGen m φ → U n θ = U m φ ∨ U n θ = -(U m φ)

/-- **PRINCIPAL THEOREM (Work Package 4), existence.**  The inherited reference family is
sign-transformation-valued. -/
theorem reference_signTransformationValued : IsSignTransformationValued refFam := by
  intro n m θ φ hn hm hP
  obtain ⟨e, he, hUn⟩ := (coincidence_iff hn hm θ φ).1 hP
  rcases he with rfl | rfl
  · exact Or.inl (by rw [refFam, refFam, hUn, one_smul])
  · exact Or.inr (by rw [refFam, refFam, hUn]; module)

/-- **DERIVED.**  The defect of the reference family on a closed visible relation is
genuinely `-1` for some pair: the sign relaxation cannot be removed. -/
theorem reference_sign_defect_nontrivial :
    ∃ (n : Vec3) (θ φ : ℝ), IsUnitAxis n ∧ PhiGen n θ = PhiGen n φ ∧
      refFam n θ = -(refFam n φ) ∧ refFam n θ ≠ refFam n φ := by
  refine ⟨(1, 0, 0), 0, 2 * Real.pi, by simp [IsUnitAxis, h3], ?_, ?_, ?_⟩
  · have h := coincidence_add_two_pi ((1, 0, 0) : Vec3) 0
    rw [zero_add] at h
    exact h.symm
  · rw [refFam, refFam, Un_zero, full_turn_val]
    module
  · rw [refFam, refFam, Un_zero, full_turn_val]
    intro hcon
    have := congrFun hcon 0
    simp [w1] at this
    linarith

/-! ## Work Package 4 — the exact surviving class is a single family -/

/-- **DERIVED.**  A full turn forces the two central rates of a regular family into the
inherited normal form.  Only the value of the family at the full turn is used. -/
theorem full_turn_forces {U : Vec3 → ℝ → W} (hU : IsRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (h2pi : U n (2 * Real.pi) = ε • w1) :
    rateAlpha U n = 0 ∧ (∃ k : ℤ, rateBeta U n = k / 2) ∧
      Real.cos (rateBeta U n * (2 * Real.pi)) = -ε := by
  have hfac := regularFamily_param_spec hU hn (2 * Real.pi)
  rw [h2pi, full_turn_val] at hfac
  have hz : zexp (rateAlpha U n) (rateBeta U n) (2 * Real.pi) = (-ε) • w1 := by
    have h3 : zexp (rateAlpha U n) (rateBeta U n) (2 * Real.pi) ⋆ (-w1) = ε • w1 := hfac.symm
    rw [mul_neg_W, mul_one_W] at h3
    have h4 := congrArg (fun t : W => -t) h3
    simp only [neg_neg] at h4
    rw [h4]
    module
  have hcoe : ((-ε) • w1 : W) = zc (-ε) 0 := by
    funext i; fin_cases i <;> simp [zc, w1, wS]
  rw [zexp, hcoe] at hz
  obtain ⟨hc, hs⟩ := zc_injective hz
  have hexp : 0 < Real.exp (rateAlpha U n * (2 * Real.pi)) := Real.exp_pos _
  have hsin : Real.sin (rateBeta U n * (2 * Real.pi)) = 0 := by
    rcases mul_eq_zero.1 hs with h' | h'
    · exact absurd h' (ne_of_gt hexp)
    · exact h'
  have hpy := Real.sin_sq_add_cos_sq (rateBeta U n * (2 * Real.pi))
  have hcos2 : Real.cos (rateBeta U n * (2 * Real.pi)) ^ 2 = 1 := by nlinarith [hpy, hsin]
  have hexp1 : Real.exp (rateAlpha U n * (2 * Real.pi)) = 1 := by
    have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hprod : (Real.exp (rateAlpha U n * (2 * Real.pi))
        * Real.cos (rateBeta U n * (2 * Real.pi))) ^ 2 = ε ^ 2 := by rw [hc]; ring
    have hsq : Real.exp (rateAlpha U n * (2 * Real.pi)) ^ 2 = 1 := by
      linear_combination hprod
        - Real.exp (rateAlpha U n * (2 * Real.pi)) ^ 2 * hcos2 + hε2
    have hfact : (Real.exp (rateAlpha U n * (2 * Real.pi)) - 1)
        * (Real.exp (rateAlpha U n * (2 * Real.pi)) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 hfact with h' | h'
    · linarith
    · linarith
  have hα : rateAlpha U n = 0 := by
    have hz0 : rateAlpha U n * (2 * Real.pi) = 0 := by
      rw [← Real.exp_zero, Real.exp_eq_exp] at hexp1
      exact hexp1
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by have := Real.pi_pos; positivity
    exact (mul_eq_zero.1 hz0).resolve_right hpi
  refine ⟨hα, ?_, by rw [hexp1, one_mul] at hc; exact hc⟩
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  refine ⟨k, ?_⟩
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp at hk ⊢
  nlinarith [hk, Real.pi_pos]

/-- **DERIVED.**  Sign-relaxed transformation-valuedness already forces the first central
rate to vanish and confines the second to the half-integers, in every direction. -/
theorem signValued_rates {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsSignTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    rateAlpha U n = 0 ∧ (∃ k : ℤ, rateBeta U n = k / 2) ∧
      Real.cos (rateBeta U n * (2 * Real.pi)) = -1 ∨
    rateAlpha U n = 0 ∧ (∃ k : ℤ, rateBeta U n = k / 2) ∧
      Real.cos (rateBeta U n * (2 * Real.pi)) = 1 := by
  have hcoin : PhiGen n (2 * Real.pi) = PhiGen n 0 := by
    rw [show (2 : ℝ) * Real.pi = 0 + 2 * Real.pi by ring]
    exact coincidence_add_two_pi n 0
  have h0 : U n 0 = w1 := (hU n hn).unit
  rcases hV n n (2 * Real.pi) 0 hn hn hcoin with h | h
  · refine Or.inl ?_
    have := full_turn_forces hU hn (ε := 1) (Or.inl rfl) (by rw [h, h0, one_smul])
    simpa using this
  · refine Or.inr ?_
    have := full_turn_forces hU hn (ε := -1) (Or.inr rfl) (by rw [h, h0]; module)
    simpa using this

/-- **DERIVED.**  Sign-relaxed transformation-valuedness forces the second central rate to
be odd under reversal of the direction.  No regularity in the direction is used. -/
theorem signValued_beta_odd {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsSignTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    rateBeta U (-n) = -rateBeta U n := by
  have hnn : IsUnitAxis (-n) := isUnitAxis_neg hn
  have hα : rateAlpha U n = 0 := by
    rcases signValued_rates hU hV hn with h | h <;> exact h.1
  have hαn : rateAlpha U (-n) = 0 := by
    rcases signValued_rates hU hV hnn with h | h <;> exact h.1
  -- for every parameter the two central factors agree up to a sign
  have hsin : ∀ θ : ℝ, Real.sin ((rateBeta U (-n) + rateBeta U n) * θ) = 0 := by
    intro θ
    have hP : PhiGen (-n) θ = PhiGen n (-θ) := PhiGen_neg_axis n θ
    have h1 := regularFamily_param_spec hU hnn θ
    have h2 := regularFamily_param_spec hU hn (-θ)
    have hUn : Un (-n) θ = Un n (-θ) := Un_neg_axis n θ
    have e1 : zexp (rateAlpha U (-n)) (rateBeta U (-n)) θ ⋆ Un n (-θ) = U (-n) θ := by
      rw [h1, hUn]
    have hkey : zexp (rateAlpha U (-n)) (rateBeta U (-n)) θ
        = zexp (rateAlpha U n) (rateBeta U n) (-θ) ∨
      zexp (rateAlpha U (-n)) (rateBeta U (-n)) θ
        = -(zexp (rateAlpha U n) (rateBeta U n) (-θ)) := by
      rcases hV (-n) n θ (-θ) hnn hn hP with h | h
      · exact Or.inl (Un_right_cancel hn (θ := -θ) (by rw [e1, h, h2]))
      · exact Or.inr (Un_right_cancel hn (θ := -θ) (by rw [e1, h, h2, neg_mul_W]))
    have hbn : Real.sin (rateBeta U (-n) * θ) * Real.cos (rateBeta U n * θ)
        + Real.cos (rateBeta U (-n) * θ) * Real.sin (rateBeta U n * θ) = 0 := by
      rcases hkey with h | h
      · rw [zexp, zexp, hα, hαn] at h
        obtain ⟨hc, hs⟩ := zc_injective h
        simp only [zero_mul, Real.exp_zero, one_mul] at hc hs
        rw [show rateBeta U n * -θ = -(rateBeta U n * θ) by ring, Real.cos_neg] at hc
        rw [show rateBeta U n * -θ = -(rateBeta U n * θ) by ring, Real.sin_neg] at hs
        rw [hc, hs]; ring
      · have hneg : (-(zexp (rateAlpha U n) (rateBeta U n) (-θ)) : W)
            = zc (-(Real.exp (rateAlpha U n * -θ) * Real.cos (rateBeta U n * -θ)))
                (-(Real.exp (rateAlpha U n * -θ) * Real.sin (rateBeta U n * -θ))) := by
          rw [zexp, zc, zc]; module
        rw [zexp, hneg, hα, hαn] at h
        obtain ⟨hc, hs⟩ := zc_injective h
        simp only [zero_mul, Real.exp_zero, one_mul] at hc hs
        rw [show rateBeta U n * -θ = -(rateBeta U n * θ) by ring, Real.cos_neg] at hc
        rw [show rateBeta U n * -θ = -(rateBeta U n * θ) by ring, Real.sin_neg] at hs
        rw [hc, hs]; ring
    rw [show (rateBeta U (-n) + rateBeta U n) * θ = rateBeta U (-n) * θ + rateBeta U n * θ by
      ring, Real.sin_add]
    exact hbn
  by_contra hcon
  set s : ℝ := rateBeta U (-n) + rateBeta U n with hs
  have hsne : s ≠ 0 := by
    intro h0
    apply hcon
    rw [hs] at h0
    linarith
  have := hsin (Real.pi / (2 * s))
  rw [show s * (Real.pi / (2 * s)) = Real.pi / 2 by field_simp, Real.sin_pi_div_two] at this
  norm_num at this

/-- **PRINCIPAL THEOREM (Work Package 4), the exact surviving class.**  A jointly regular
family is sign-transformation-valued **iff** it is the inherited reference family on every
unit direction.  The class that survives Packages 2 and 3 therefore consists of exactly one
family; no continuous central residual freedom remains. -/
theorem signValued_eq_reference {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsSignTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    U n θ = refFam n θ := by
  obtain ⟨m, hm, hnm⟩ := exists_unit_orthogonal hn
  have hβ := jointlyRegular_beta_continuous hU
  set γ : ℝ → Sph := fun t => ⟨circPath n m t, circPath_isUnitAxis hn hm hnm t⟩ with hγ
  have hγc : Continuous γ := (continuous_circPath n m).subtype_mk _
  have hgc : Continuous fun t : ℝ => 2 * rateBeta U ((γ t : Sph) : Vec3) :=
    (continuous_const.mul (hβ.comp hγc))
  have hint : ∀ t : ℝ, ∃ k : ℤ, 2 * rateBeta U ((γ t : Sph) : Vec3) = (k : ℝ) + 0 := by
    intro t
    obtain ⟨k, hk⟩ : ∃ k : ℤ, rateBeta U ((γ t : Sph) : Vec3) = (k : ℝ) / 2 := by
      rcases signValued_rates hU.toRegularFamily hV
        (circPath_isUnitAxis hn hm hnm t) with h | h <;> exact h.2.1
    exact ⟨k, by rw [hk]; ring⟩
  have hends := eq_of_continuous_int_shift hgc hint (a := 0) (b := Real.pi)
    (le_of_lt Real.pi_pos)
  have h0 : ((γ 0 : Sph) : Vec3) = n := by rw [hγ]; simp
  have hpi : ((γ Real.pi : Sph) : Vec3) = -n := by rw [hγ]; exact circPath_pi n m
  rw [h0, hpi, signValued_beta_odd hU.toRegularFamily hV hn] at hends
  have hβ0 : rateBeta U n = 0 := by linarith
  have hα0 : rateAlpha U n = 0 := by
    rcases signValued_rates hU.toRegularFamily hV hn with h | h <;> exact h.1
  rw [regularFamily_param_spec hU.toRegularFamily hn θ, hα0, hβ0, zexp_zero_eq, one_mul_W,
    refFam]

/-! ## Work Package 4 — the exact class of surviving central values -/

/-- **PRINCIPAL THEOREM (Work Package 4).**  Under the strongest surviving regularity class,
the central discrepancy attached to a *closed visible relation* takes values exactly in the
two-element subset `{1, -1}` of the central units.  It does not remain all of `Z^×`, it is
not a continuous subclass, and it does not depend on any path or representative choice — it
is completely determined by the axis–parameter data through the coincidence relation. -/
theorem signValued_defect_pm_one {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsSignTransformationValued U) {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    {θ φ : ℝ} (hP : PhiGen n θ = PhiGen m φ) :
    ∃ c : W, (c = w1 ∨ c = -w1) ∧ c ∈ Z ∧ U n θ = c ⋆ U m φ := by
  obtain ⟨e, he, hUn⟩ := (coincidence_iff hn hm θ φ).1 hP
  have hUnθ : U n θ = refFam n θ := signValued_eq_reference hU hV hn θ
  have hUmφ : U m φ = refFam m φ := signValued_eq_reference hU hV hm φ
  rcases he with rfl | rfl
  · refine ⟨w1, Or.inl rfl, NullSectorTask09.w1_mem_Z, ?_⟩
    rw [hUnθ, hUmφ, refFam, refFam, hUn, one_smul, one_mul_W]
  · refine ⟨-w1, Or.inr rfl, Submodule.neg_mem _ NullSectorTask09.w1_mem_Z, ?_⟩
    rw [hUnθ, hUmφ, refFam, refFam, hUn, neg_mul_W, one_mul_W]
    module

/-- **NEGATIVE CONTROL (Work Package 4).**  Without the sign normalization the coincidence
defect is *not* discrete: an explicit jointly regular family realizes a central factor of
arbitrary modulus on a closed visible relation. -/
theorem defect_not_discrete_without_normalization :
    ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧
      ∃ (n : Vec3) (θ φ : ℝ), IsUnitAxis n ∧ PhiGen n θ = PhiGen n φ ∧
        U n θ = (-(Real.exp (2 * Real.pi))) • U n φ ∧
        (-(Real.exp (2 * Real.pi))) ≠ 1 ∧ (-(Real.exp (2 * Real.pi))) ≠ -1 := by
  refine ⟨famOf (fun _ => 1) (fun _ => 0),
    jointlyRegular_famOf continuous_const continuous_const,
    (1, 0, 0), 2 * Real.pi, 0, by simp [IsUnitAxis, h3], ?_, ?_, ?_, ?_⟩
  · have h := coincidence_add_two_pi ((1, 0, 0) : Vec3) 0
    rw [zero_add] at h
    exact h
  · have hz2 : zexp 1 0 (2 * Real.pi) = Real.exp (2 * Real.pi) • w1 := by
      rw [zexp]
      simp only [one_mul, zero_mul, Real.cos_zero, Real.sin_zero, mul_zero, mul_one]
      funext i; fin_cases i <;> simp [zc, w1, wS]
    rw [famOf, famOf, zexp_zero, Un_zero, one_mul_W, full_turn_val, hz2, smul_mul_W,
      mul_neg_W, mul_one_W]
    module
  · have := Real.add_one_le_exp (x := 2 * Real.pi)
    have hpi := Real.pi_pos
    intro hcon; linarith
  · have hpos := Real.exp_pos (2 * Real.pi)
    have := Real.add_one_le_exp (x := 2 * Real.pi)
    have hpi := Real.pi_pos
    intro hcon; linarith

/-! ## Finite consistency identities, from associativity alone -/

/-- **DERIVED.**  For every axis lift the same-axis composition defect is trivial: the
one-axis group law leaves no room for a discrepancy. -/
theorem defect_same_axis_trivial {U : Vec3 → ℝ → W} (hU : IsRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ φ : ℝ) : U n θ ⋆ U n φ = U n (θ + φ) :=
  ((hU n hn).group θ φ).symm

/-- **DERIVED.**  The central sign defects of a chain of coincidences compose.  This is the
finite consistency identity forced by associativity of the inherited product; it is stated
without any quotient. -/
theorem defect_chain {x y z c d : W} (hxy : x = c ⋆ y) (hyz : y = d ⋆ z) :
    x = (c ⋆ d) ⋆ z := by
  rw [hxy, hyz, mul_assoc_W]

end NullSectorTask16
