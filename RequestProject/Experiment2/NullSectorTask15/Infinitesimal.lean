import RequestProject.Experiment2.NullSectorTask15.MixedComposition

/-!
# Task 15, Layer 4 (§V): the infinitesimal central residual and its direction dependence

Only now, after the finite regular composition law of Layer 3, is the derivative at the
identity taken.

For every unit axis the regular lift has an exact left generator

```
(d/dθ) U n θ |_{θ = 0} = C n − (1/2) • J n ,     C n = α n • 1 + β n • S ∈ Z ,
```

with `C n` written uniquely in the inherited real basis `1, S` of the exact centre.

The classification questions **A–F** of §V are then answered:

* the two real functions `α, β` of the direction are **completely free**
  (`regular_family_arbitrary_parameters`): every pair of real functions on the set of unit
  axes is realized by a regular multi-axis lift, so mixed-axis coherence imposes no
  relation whatsoever between different directions — answer **C**;
* if, in addition, the lift is required to be a genuine function of the *transformation*
  (equal automorphisms must receive equal implementers), then exactly two relations are
  forced and no more: `α ≡ 0` and `β n ∈ ℤ + 1/2` (`autValued_forces_alpha_zero`,
  `autValued_forces_beta_half_odd`), together with the antipodal oddness
  (`autValued_antipodal_odd`) — answer **D** for that stronger notion.

Nothing is normalized because a convenient reference lift exists: the reference lift is the
member `α = β = 0` of the family and is never used to fix the parameters.
-/

namespace NullSectorTask15

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14

/-! ## Elementary derivatives -/

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

/-! ## §V — the exact left generator of a regular axis lift -/

/-- **PRINCIPAL THEOREM (§V): the exact left generator.**  The derivative at the identity
parameter of the classified regular axis lift is the central residual generator plus the
inherited reference generator `-(1/2) J n`. -/
theorem hasDerivAt_regularLift_zero (n : Vec3) (α β : ℝ) :
    HasDerivAt (fun θ => zexp α β θ ⋆ Un n θ) (zc α β - (2⁻¹ : ℝ) • Jmap n) 0 := by
  have he : (fun θ => zexp α β θ ⋆ Un n θ) = fun θ : ℝ =>
      (Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) • w1
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) • wS
      + (-(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2))) • Jmap n
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) • spat n := by
    funext θ
    exact zc_mul_Un n (Real.exp (α * θ) * Real.cos (β * θ))
      (Real.exp (α * θ) * Real.sin (β * θ)) θ
  rw [he]
  have dA : HasDerivAt
      (fun θ : ℝ => Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) α 0 := by
    simpa using ((hasDerivAt_expc α 0).mul (hasDerivAt_cosc β 0)).mul (hasDerivAt_cosh2 0)
  have dB : HasDerivAt
      (fun θ : ℝ => Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) β 0 := by
    simpa using ((hasDerivAt_expc α 0).mul (hasDerivAt_sinc β 0)).mul (hasDerivAt_cosh2 0)
  have dC : HasDerivAt
      (fun θ : ℝ => -(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2)))
      (-(2⁻¹ : ℝ)) 0 := by
    have h := ((hasDerivAt_expc α 0).mul (hasDerivAt_cosc β 0)).mul (hasDerivAt_sinh2 0)
    simpa using h.neg
  have dD : HasDerivAt
      (fun θ : ℝ => Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) 0 0 := by
    simpa using ((hasDerivAt_expc α 0).mul (hasDerivAt_sinc β 0)).mul (hasDerivAt_sinh2 0)
  have h := (((dA.smul_const w1).add (dB.smul_const wS)).add
    (dC.smul_const (Jmap n))).add (dD.smul_const (spat n))
  refine h.congr_deriv ?_
  rw [zc]
  module

/-! ## §V — regular multi-axis lift families and their parameter functions -/

/-- **NEUTRAL DEFINITION (§V).**  A regular multi-axis lift: for *every* unit spatial
direction a continuous internal implementation of the inherited automorphism family of that
direction.  No relation between different directions is imposed. -/
def IsRegularFamily (U : Vec3 → ℝ → W) : Prop :=
  ∀ n : Vec3, IsUnitAxis n → IsContinuousAxisLift n (U n)

/-- **DERIVED (§V).**  The two real parameters attached to each unit direction by the
Layer-1 classification. -/
noncomputable def paramPair (U : Vec3 → ℝ → W) (n : Vec3) : ℝ × ℝ :=
  open Classical in
  if h : ∃ p : ℝ × ℝ, ∀ θ, U n θ = zexp p.1 p.2 θ ⋆ Un n θ then h.choose else (0, 0)

/-- **NEUTRAL DEFINITION (§V).**  The first central rate of a regular family. -/
noncomputable def rateAlpha (U : Vec3 → ℝ → W) (n : Vec3) : ℝ := (paramPair U n).1

/-- **NEUTRAL DEFINITION (§V).**  The second central rate of a regular family. -/
noncomputable def rateBeta (U : Vec3 → ℝ → W) (n : Vec3) : ℝ := (paramPair U n).2

/-- **PRINCIPAL THEOREM (§V): every regular family has exactly two real rates per
direction.** -/
theorem regularFamily_param_spec {U : Vec3 → ℝ → W} (hU : IsRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) :
    U n θ = zexp (rateAlpha U n) (rateBeta U n) θ ⋆ Un n θ := by
  have hex : ∃ p : ℝ × ℝ, ∀ θ, U n θ = zexp p.1 p.2 θ ⋆ Un n θ := by
    obtain ⟨α, β, hUe⟩ := (continuousAxisLift_classification hn (U n)).1 (hU n hn)
    exact ⟨(α, β), hUe⟩
  have h : paramPair U n = hex.choose := by
    rw [paramPair, dif_pos hex]
  rw [rateAlpha, rateBeta, h]
  exact hex.choose_spec θ

/-- **DERIVED (§V).**  The two rates are uniquely determined. -/
theorem regularFamily_param_unique {U : Vec3 → ℝ → W} (hU : IsRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) {α β : ℝ} (h : ∀ θ, U n θ = zexp α β θ ⋆ Un n θ) :
    α = rateAlpha U n ∧ β = rateBeta U n :=
  continuousAxisLift_parameters_unique hn
    fun θ => (h θ).symm.trans (regularFamily_param_spec hU hn θ)

/-- **NEUTRAL DEFINITION (§V).**  The central infinitesimal residual of a regular family in
the direction `n`, an element of the exact centre. -/
noncomputable def centralResidual (U : Vec3 → ℝ → W) (n : Vec3) : W :=
  zc (rateAlpha U n) (rateBeta U n)

theorem centralResidual_mem_Z (U : Vec3 → ℝ → W) (n : Vec3) : centralResidual U n ∈ Z :=
  zc_mem_Z _ _

/-- **PRINCIPAL THEOREM (§V): isolation of the central infinitesimal residual.**  The
generator of a regular family splits uniquely into the central residual `C n = α n • 1 +
β n • S` and the inherited reference generator; the two central coefficients are unique. -/
theorem regularFamily_generator {U : Vec3 → ℝ → W} (hU : IsRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) :
    HasDerivAt (U n) (centralResidual U n - (2⁻¹ : ℝ) • Jmap n) 0 ∧
      centralResidual U n = rateAlpha U n • w1 + rateBeta U n • wS ∧
      ∀ a b : ℝ, centralResidual U n = a • w1 + b • wS →
        a = rateAlpha U n ∧ b = rateBeta U n := by
  refine ⟨?_, rfl, fun a b hab => ?_⟩
  · have he : U n = fun θ => zexp (rateAlpha U n) (rateBeta U n) θ ⋆ Un n θ :=
      funext fun θ => regularFamily_param_spec hU hn θ
    rw [he, centralResidual]
    exact hasDerivAt_regularLift_zero n _ _
  · have h : zc (rateAlpha U n) (rateBeta U n) = zc a b := hab
    exact ⟨(zc_injective h).1.symm, (zc_injective h).2.symm⟩

/-! ## §V — answer C: the two rates are free functions of the direction -/

/-- **NEUTRAL DEFINITION.**  The regular family attached to a pair of real functions of the
direction. -/
noncomputable def famOf (a b : Vec3 → ℝ) (n : Vec3) (θ : ℝ) : W :=
  zexp (a n) (b n) θ ⋆ Un n θ

/-- **PRINCIPAL THEOREM (§V), answer **C**: no mixed-axis relation between directions.**
*Every* pair of real functions of the unit direction — with no continuity, no symmetry and
no relation between different directions — is realized by a regular multi-axis lift, and
the realized rates are exactly those functions.  Hence multi-axis coherence imposes no
relation whatsoever on the central rates. -/
theorem regular_family_arbitrary_parameters (a b : Vec3 → ℝ) :
    IsRegularFamily (famOf a b) ∧
      ∀ n : Vec3, IsUnitAxis n →
        rateAlpha (famOf a b) n = a n ∧ rateBeta (famOf a b) n = b n := by
  have hfam : IsRegularFamily (famOf a b) := by
    intro n hn
    exact (continuousAxisLift_classification hn (famOf a b n)).2 ⟨a n, b n, fun _ => rfl⟩
  refine ⟨hfam, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := regularFamily_param_unique hfam hn (α := a n) (β := b n) (fun _ => rfl)
  exact ⟨h1.symm, h2.symm⟩

/-- **PRINCIPAL THEOREM (§V), negative control.**  Two regular families may have completely
unrelated central residuals in two different directions; in particular no relation of the
form `α n = α m` or `β n = β m` is derivable. -/
theorem central_rates_independent_across_axes {n m : Vec3} (hn : IsUnitAxis n)
    (hm : IsUnitAxis m) (hnm : n ≠ m) (a₁ b₁ a₂ b₂ : ℝ) :
    ∃ U : Vec3 → ℝ → W, IsRegularFamily U ∧
      rateAlpha U n = a₁ ∧ rateBeta U n = b₁ ∧ rateAlpha U m = a₂ ∧ rateBeta U m = b₂ := by
  classical
  refine ⟨famOf (fun k => if k = n then a₁ else a₂) (fun k => if k = n then b₁ else b₂), ?_⟩
  obtain ⟨hfam, hpar⟩ := regular_family_arbitrary_parameters
    (fun k => if k = n then a₁ else a₂) (fun k => if k = n then b₁ else b₂)
  refine ⟨hfam, ?_, ?_, ?_, ?_⟩
  · rw [(hpar n hn).1]; simp
  · rw [(hpar n hn).2]; simp
  · rw [(hpar m hm).1]; simp [Ne.symm hnm]
  · rw [(hpar m hm).2]; simp [Ne.symm hnm]

/-! ## §V — the stronger transformation-valued notion -/

theorem isUnitAxis_neg {n : Vec3} (hn : IsUnitAxis n) : IsUnitAxis (-n) := by
  simp only [IsUnitAxis, h3, dot3_apply] at hn ⊢
  simp only [Prod.fst_neg, Prod.snd_neg]
  nlinarith [hn]

theorem Jmap_neg (n : Vec3) : Jmap (-n) = -Jmap n := by
  have h : Jmap ((-1 : ℝ) • n) = (-1 : ℝ) • Jmap n := Jmap_linear.2 (-1) n
  rw [neg_one_smul] at h
  rw [h]
  module

/-- **DERIVED.**  Reversing the axis is the same as reversing the parameter, already at the
level of the inherited reference implementation. -/
theorem Un_neg_axis (n : Vec3) (θ : ℝ) : Un (-n) θ = Un n (-θ) := by
  rw [Un, Un_neg, Jmap_neg]
  module

/-- **DERIVED.**  Consequently the inherited automorphism families of `n` and `-n` are the
same family with reversed parameter. -/
theorem PhiGen_neg_axis (n : Vec3) (θ : ℝ) : PhiGen (-n) θ = PhiGen n (-θ) := by
  refine LinearMap.ext (fun x => ?_)
  show (Un (-n) θ ⋆ x) ⋆ Un (-n) (-θ) = (Un n (-θ) ⋆ x) ⋆ Un n (-(-θ))
  rw [Un_neg_axis, Un_neg_axis]

/-- **DERIVED.**  A full turn of the parameter leaves the inherited automorphism
unchanged. -/
theorem PhiGen_two_pi (n : Vec3) : PhiGen n (2 * Real.pi) = PhiGen n 0 := by
  rw [full_turn_aut]
  refine (LinearMap.ext (fun x => ?_)).symm
  show (Un n 0 ⋆ x) ⋆ Un n (-0) = x
  rw [neg_zero, Un_zero, one_mul_W, mul_one_W]

/-- **NEUTRAL DEFINITION (§V, stronger notion).**  A lift assignment that is a genuine
function of the implemented transformation: equal inherited automorphisms receive equal
internal implementers. -/
def IsTransformationValued (U : Vec3 → ℝ → W) : Prop :=
  ∀ (n m : Vec3) (θ φ : ℝ), IsUnitAxis n → IsUnitAxis m →
    PhiGen n θ = PhiGen m φ → U n θ = U m φ

/-- **DERIVED.**  A transformation-valued regular family has central residual `-1` after a
full turn of the parameter. -/
theorem transformationValued_full_turn {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    zexp (rateAlpha U n) (rateBeta U n) (2 * Real.pi) = -w1 := by
  have h0 : U n 0 = w1 := (hU n hn).unit
  have h2 : U n (2 * Real.pi) = w1 := by
    rw [hV n n (2 * Real.pi) 0 hn hn (PhiGen_two_pi n), h0]
  have hfac := regularFamily_param_spec hU hn (2 * Real.pi)
  rw [h2, full_turn_val] at hfac
  have h3 : zexp (rateAlpha U n) (rateBeta U n) (2 * Real.pi) ⋆ (-w1) = w1 := hfac.symm
  rw [mul_neg_W, mul_one_W] at h3
  have h4 := congrArg (fun t : W => -t) h3
  simpa using h4

/-- **DERIVED (§V).**  The two real coefficient equations forced by a full turn. -/
theorem transformationValued_full_turn_coeffs {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    Real.exp (rateAlpha U n * (2 * Real.pi)) * Real.cos (rateBeta U n * (2 * Real.pi)) = -1 ∧
      Real.exp (rateAlpha U n * (2 * Real.pi)) *
        Real.sin (rateBeta U n * (2 * Real.pi)) = 0 := by
  have h := transformationValued_full_turn hU hV hn
  have hneg : (-w1 : W) = zc (-1) 0 := by
    funext i; fin_cases i <;> simp [zc, w1, wS]
  rw [zexp, hneg] at h
  exact zc_injective h

/-- **DERIVED (§V).**  In the transformation-valued case the two trigonometric values after
a full turn are completely determined. -/
theorem transformationValued_sin_cos {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    Real.sin (rateBeta U n * (2 * Real.pi)) = 0 ∧
      Real.cos (rateBeta U n * (2 * Real.pi)) = -1 ∧
      Real.exp (rateAlpha U n * (2 * Real.pi)) = 1 := by
  obtain ⟨hc, hs⟩ := transformationValued_full_turn_coeffs hU hV hn
  have hexp : 0 < Real.exp (rateAlpha U n * (2 * Real.pi)) := Real.exp_pos _
  have hsin : Real.sin (rateBeta U n * (2 * Real.pi)) = 0 := by
    rcases mul_eq_zero.1 hs with h' | h'
    · exact absurd h' (ne_of_gt hexp)
    · exact h'
  have hpy := Real.sin_sq_add_cos_sq (rateBeta U n * (2 * Real.pi))
  have hsq : Real.cos (rateBeta U n * (2 * Real.pi)) ^ 2 = 1 := by nlinarith [hpy, hsin]
  have hcos : Real.cos (rateBeta U n * (2 * Real.pi)) = -1 := by
    rcases mul_eq_zero.1 (by nlinarith [hsq] :
        (Real.cos (rateBeta U n * (2 * Real.pi)) - 1) *
          (Real.cos (rateBeta U n * (2 * Real.pi)) + 1) = 0) with h' | h'
    · exfalso
      have hc1 : Real.cos (rateBeta U n * (2 * Real.pi)) = 1 := by linarith
      rw [hc1, mul_one] at hc
      linarith
    · linarith
  refine ⟨hsin, hcos, ?_⟩
  rw [hcos] at hc
  linarith

/-- **PRINCIPAL THEOREM (§V), answer **D** for the stronger notion, part 1.**  A
transformation-valued regular family has vanishing first central rate in every direction:
`α` is uniquely normalized, and this is *derived*, not chosen. -/
theorem autValued_forces_alpha_zero {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) : rateAlpha U n = 0 := by
  obtain ⟨-, -, hone⟩ := transformationValued_sin_cos hU hV hn
  have hz : rateAlpha U n * (2 * Real.pi) = 0 := by
    rw [← Real.exp_zero, Real.exp_eq_exp] at hone
    exact hone
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by
    have := Real.pi_pos; positivity
  exact (mul_eq_zero.1 hz).resolve_right hpi

/-- **PRINCIPAL THEOREM (§V), answer **D** for the stronger notion, part 2.**  The second
central rate of a transformation-valued regular family is confined to the *discrete* set of
half-odd integers.  It is not forced to a single value: the freedom survives, but only in a
discrete form. -/
theorem autValued_forces_beta_half_odd {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    ∃ k : ℤ, rateBeta U n = k + 1 / 2 := by
  obtain ⟨hsin, hcos, -⟩ := transformationValued_sin_cos hU hV hn
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hsin
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hbeta : rateBeta U n = (m : ℝ) / 2 := by
    field_simp at hm ⊢
    nlinarith [hm, Real.pi_pos]
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · exfalso
    have hcast : (m : ℝ) = 2 * (j : ℝ) := by rw [hj]; push_cast; ring
    have : rateBeta U n * (2 * Real.pi) = (j : ℝ) * (2 * Real.pi) := by
      rw [hbeta, hcast]; ring
    rw [this, Real.cos_int_mul_two_pi] at hcos
    norm_num at hcos
  · refine ⟨j, ?_⟩
    have hcast : (m : ℝ) = 2 * (j : ℝ) + 1 := by rw [hj]; push_cast; ring
    rw [hbeta, hcast]; ring

/-- **DERIVED.**  Reversing the axis reverses both parameters of the exponential–rotation
family. -/
theorem zexp_neg_param (α β θ : ℝ) : zexp α β (-θ) = zexp (-α) (-β) θ := by
  have h1 : α * -θ = -α * θ := by ring
  have h2 : β * -θ = -β * θ := by ring
  rw [zexp, zexp, h1, h2]

/-- **PRINCIPAL THEOREM (§V), answer **D** for the stronger notion, part 3.**  A
transformation-valued regular family has *odd* central rates under reversal of the axis.
This is the only relation between different directions that the inherited data forces. -/
theorem autValued_antipodal_odd {U : Vec3 → ℝ → W} (hU : IsRegularFamily U)
    (hV : IsTransformationValued U) {n : Vec3} (hn : IsUnitAxis n) :
    rateAlpha U (-n) = -rateAlpha U n ∧ rateBeta U (-n) = -rateBeta U n := by
  have hnn : IsUnitAxis (-n) := isUnitAxis_neg hn
  have key : ∀ θ : ℝ,
      zexp (rateAlpha U (-n)) (rateBeta U (-n)) θ
        = zexp (-rateAlpha U n) (-rateBeta U n) θ := by
    intro θ
    have hval : U (-n) θ = U n (-θ) :=
      hV (-n) n θ (-θ) hnn hn (PhiGen_neg_axis n θ)
    have h1 := regularFamily_param_spec hU hnn θ
    have h2 := regularFamily_param_spec hU hn (-θ)
    rw [hval, h2, Un_neg_axis] at h1
    have hcan := Un_right_cancel hn (θ := -θ) h1.symm
    rw [← zexp_neg_param]
    exact hcan
  obtain ⟨h1, h2⟩ := zexp_injective key
  exact ⟨h1, h2⟩

/-! ## §V — the classification verdict -/

/-- **PRINCIPAL THEOREM (§V): the exact answer to the alternatives A–F.**

* **(1)** For regular lifts indexed by a direction and a parameter, the two central rates
  are two completely free real functions of the direction: every pair is realized, so
  neither **A** (a unique normalization) nor **B** (two global constants) holds, and the
  correct answer is **C**.
* **(2)** If the lift is in addition required to be a genuine function of the implemented
  transformation, then exactly the relations `α ≡ 0`, `β n ∈ ℤ + 1/2` and antipodal
  oddness are forced — answer **D** for that stronger notion; the first rate is closed and
  the second survives discretely. -/
theorem central_rate_classification :
    (∀ a b : Vec3 → ℝ, IsRegularFamily (famOf a b) ∧
        ∀ n : Vec3, IsUnitAxis n →
          rateAlpha (famOf a b) n = a n ∧ rateBeta (famOf a b) n = b n) ∧
      (∀ U : Vec3 → ℝ → W, IsRegularFamily U → IsTransformationValued U →
        ∀ n : Vec3, IsUnitAxis n →
          rateAlpha U n = 0 ∧ (∃ k : ℤ, rateBeta U n = k + 1 / 2) ∧
            rateBeta U (-n) = -rateBeta U n) :=
  ⟨fun a b => regular_family_arbitrary_parameters a b,
    fun _ hU hV _ hn => ⟨autValued_forces_alpha_zero hU hV hn,
      autValued_forces_beta_half_odd hU hV hn, (autValued_antipodal_odd hU hV hn).2⟩⟩

end NullSectorTask15
