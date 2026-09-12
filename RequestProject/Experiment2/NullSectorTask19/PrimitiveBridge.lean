import RequestProject.Experiment2.NullSectorTask19.SafeBase

/-!
# Task 19, Package A and Package B: a primitive bridge notion independent of exactness

The Task-18 predicate `IsGlobalBridge` contains global exactness **in its definition**, so
the Task-18 statement "no global bridge exists" cannot by itself be read as an intrinsic
obstruction: it denies the existence of an object whose definition already contains the
property whose failure is at issue.  Task 19 therefore replaces it.

## Package A (§10–§18)

* §10, §11.  `IsPrimitiveBridge c` is defined by **four intrinsic properties of the factor
  itself**: centrality at every unit direction, normalization at parameter zero,
  one-parameter multiplicativity, and joint continuity in direction and parameter.  Nothing
  about the reconstructed family `recon c := c ⋆ refFam` is required, and in particular no
  exactness of any kind.
* §12.  The two rates are kept **explicit**: `primRateA c` and `primRateB c` are the
  already inherited recovered rate functions of the reconstructed family, not the output of
  an existential.
* §13.  Exact normal form: every primitive bridge is `c n θ = zexp (primRateA c n)
  (primRateB c n) θ`, and the pair of rates realizing it is unique.
* §14.  A primitive bridge is determined by the **pair** of its rates, and is **not**
  determined by the directional rate `primRateB` alone: an explicit counterexample is given.
  So the answer to "is every primitive bridge determined by its rate?" is *no* for the
  directional rate and *yes* for the pair.
* §15.  The additional rate property equivalent to local exactness of the reconstructed
  family is: the first rate vanishes and the directional rate is half-odd, at every unit
  direction.  Both directions are proved.
* §16.  The additional property equivalent to global exactness is the same, plus reversal
  oddness of the directional rate.  Both directions are proved.
* §17.  The three implications are stated separately.
* §18.  Nothing is called an equivalence unless both directions appear in the statement.

## Package B (§19–§24)

* §19.  `IsGlobalRate b` — continuity on all unit directions, half-oddness at every unit
  direction, reversal oddness.
* §20.  `(∃ primitive bridge whose reconstruction is globally exact) ↔ (∃ global rate)`:
  **proved**, both directions.
* §21.  `(∃ such a primitive bridge) ↔ (∃ globally jointly regular exact family)`:
  **proved**, both directions; the backward direction takes the derived bridge of the
  family, whose primitivity is established here without assuming exactness anywhere in the
  definition.
* §23.  The misleading Task-18 endpoint `no_global_bridge_iff_no_rate` — whose statement is
  a *conjunction* of two negations, not an equivalence — is replaced by two theorems whose
  names match their statements: the genuine equivalence `primitiveBridge_iff_globalRate`
  and the conjunction `no_global_rate_and_no_primitive_global_bridge`.
* §24.  No nonexistence statement here is obtained by inserting exactness into a
  definition: primitive bridges **exist** (`exists_primitiveBridge`), and even locally
  exact ones exist; only the globally exact reconstruction fails.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## §10, §11 — the primitive notion -/

/-- **NEUTRAL DEFINITION (§10, §11).**  A *primitive bridge candidate*: a factor, indexed by
direction and parameter, which is central at every unit direction, normalized at the
identity parameter, multiplicative in the parameter along each direction, and jointly
continuous.  Nothing about the family it reconstructs is required; in particular exactness
does **not** occur in this definition. -/
structure IsPrimitiveBridge (c : Vec3 → ℝ → W) : Prop where
  /-- centrality at every unit direction -/
  central : ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, c n θ ∈ Z
  /-- normalization at parameter zero -/
  unit : ∀ n : Vec3, IsUnitAxis n → c n 0 = w1
  /-- one-parameter multiplicativity -/
  mul : ∀ n : Vec3, IsUnitAxis n → ∀ θ φ : ℝ, c n (θ + φ) = c n θ ⋆ c n φ
  /-- continuous dependence on direction and parameter -/
  cont : Continuous fun p : Sph × ℝ => c (p.1 : Vec3) p.2

/-- **NEUTRAL DEFINITION.**  The family reconstructed from a factor and the unique global
sign-relaxed reference. -/
noncomputable def recon (c : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) : W := c n θ ⋆ refFam n θ

theorem recon_apply (c : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) :
    recon c n θ = c n θ ⋆ refFam n θ := rfl

theorem IsPrimitiveBridge.mul_neg {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) : c n θ ⋆ c n (-θ) = w1 := by
  have h := hc.mul n hn θ (-θ)
  rw [add_neg_cancel, hc.unit n hn] at h
  exact h.symm

/-! ## §17, first implication — a primitive bridge reconstructs a jointly regular family -/

/-- **PRINCIPAL THEOREM (§17a).**  Every primitive bridge reconstructs a **jointly regular
family**.  Only the four intrinsic properties are used. -/
theorem primitiveBridge_jointlyRegular {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) :
    IsJointlyRegularFamily (recon c) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · have hUn : IsAxisLift n (refFam n) := refFam_jointlyRegular.lift n hn
    refine ⟨?_, ?_, ?_⟩
    · show c n 0 ⋆ refFam n 0 = w1
      rw [hc.unit n hn, hUn.unit, mul_one_W]
    · intro θ φ
      show c n (θ + φ) ⋆ refFam n (θ + φ) = (c n θ ⋆ refFam n θ) ⋆ (c n φ ⋆ refFam n φ)
      rw [hc.mul n hn θ φ, hUn.group θ φ, central_swap_mul (hc.central n hn φ)]
    · intro θ x
      show ((c n θ ⋆ refFam n θ) ⋆ x) ⋆ (c n (-θ) ⋆ refFam n (-θ)) = PhiGen n θ x
      rw [mul_assoc_W (c n θ) (refFam n θ) x,
        central_swap_mul (hc.central n hn (-θ)), hc.mul_neg hn θ, one_mul_W]
      exact hUn.conj θ x
  · exact continuous_starW hc.cont refFam_jointlyRegular.joint

/-! ## §12 — the two rates, explicit -/

/-- **NEUTRAL DEFINITION (§12).**  The first rate of a primitive bridge: the already
inherited recovered rate of the reconstructed family.  It is an explicit function, not the
output of an existential. -/
noncomputable def primRateA (c : Vec3 → ℝ → W) (n : Vec3) : ℝ := rateAlpha (recon c) n

/-- **NEUTRAL DEFINITION (§12).**  The directional rate of a primitive bridge. -/
noncomputable def primRateB (c : Vec3 → ℝ → W) (n : Vec3) : ℝ := rateBeta (recon c) n

/-! ## §13 — the exact normal form -/

/-- **PRINCIPAL THEOREM (§13).**  Every primitive bridge is exactly the inherited central
one-parameter element of its two rates.  The normal form is *derived*; no shape is assumed
in the definition. -/
theorem primitiveBridge_normal_form {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) : c n θ = zexp (primRateA c n) (primRateB c n) θ :=
  Un_right_cancel hn (recovered_form (primitiveBridge_jointlyRegular hc) hn θ)

/-- **PRINCIPAL THEOREM (§13), uniqueness of the pair.**  The two rates realizing the
normal form are unique. -/
theorem primitiveBridge_rates_unique {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) {n : Vec3}
    (hn : IsUnitAxis n) {α β : ℝ} (h : ∀ θ : ℝ, c n θ = zexp α β θ) :
    α = primRateA c n ∧ β = primRateB c n := by
  refine zexp_injective (fun θ => ?_)
  rw [← h θ, primitiveBridge_normal_form hc hn θ]

/-! ## §14 — what the rates determine -/

/-- **PRINCIPAL THEOREM (§14), positive half.**  A primitive bridge is determined by the
**pair** of its rates: two primitive bridges with the same two rates coincide at every unit
direction and every parameter. -/
theorem primitiveBridge_ext {c d : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c)
    (hd : IsPrimitiveBridge d) {n : Vec3} (hn : IsUnitAxis n)
    (hA : primRateA c n = primRateA d n) (hB : primRateB c n = primRateB d n) (θ : ℝ) :
    c n θ = d n θ := by
  rw [primitiveBridge_normal_form hc hn θ, primitiveBridge_normal_form hd hn θ, hA, hB]

/-- **NEUTRAL DEFINITION.**  The direction-independent primitive bridge attached to a pair
of real numbers. -/
noncomputable def cexp (a b : ℝ) : Vec3 → ℝ → W := fun _ θ => zexp a b θ

theorem cexp_isPrimitiveBridge (a b : ℝ) : IsPrimitiveBridge (cexp a b) where
  central := fun _ _ θ => zexp_mem_Z a b θ
  unit := fun _ _ => zexp_zero a b
  mul := fun _ _ θ φ => (zexp_isCentralHom a b).mul θ φ
  cont := (zexp_continuous a b).comp continuous_snd

theorem cexp_rates (a b : ℝ) {n : Vec3} (hn : IsUnitAxis n) :
    primRateA (cexp a b) n = a ∧ primRateB (cexp a b) n = b := by
  obtain ⟨h1, h2⟩ := primitiveBridge_rates_unique (cexp_isPrimitiveBridge a b) hn
    (α := a) (β := b) (fun _ => rfl)
  exact ⟨h1.symm, h2.symm⟩

/-- **PRINCIPAL THEOREM (§14), negative half: REFUTATION.**  A primitive bridge is **not**
determined by its directional rate alone.  Two primitive bridges have the same directional
rate `0` at every unit direction and are different. -/
theorem primitiveBridge_not_determined_by_directional_rate :
    ∃ c d : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsPrimitiveBridge d ∧
      (∀ n : Vec3, IsUnitAxis n → primRateB c n = primRateB d n) ∧
      ∃ n : Vec3, IsUnitAxis n ∧ ∃ θ : ℝ, c n θ ≠ d n θ := by
  refine ⟨cexp 1 0, cexp 0 0, cexp_isPrimitiveBridge 1 0, cexp_isPrimitiveBridge 0 0,
    fun n hn => by rw [(cexp_rates 1 0 hn).2, (cexp_rates 0 0 hn).2], e1, e1_isUnitAxis, 1, ?_⟩
  show zexp 1 0 1 ≠ zexp 0 0 1
  rw [zexp, zexp]
  intro hcon
  have h := (zc_injective hcon).1
  simp only [mul_one, Real.cos_zero, Real.exp_zero] at h
  have h1 : Real.exp 1 = 1 := by linarith
  have h2 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num)
    linarith
  rw [h1] at h2
  exact absurd h2 (lt_irrefl 1)

/-! ## The derived bridge of a jointly regular family is a primitive bridge -/

/-- **DERIVED.**  The Task-18 bridge of an arbitrary jointly regular family is the central
one-parameter element of the two recovered rates.  (Task 18 proved this only under the
extra hypothesis that the first rate vanishes.) -/
theorem bridge_eq_zexp_general {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) :
    Bridge U n θ = zexp (rateAlpha U n) (rateBeta U n) θ := by
  have h := recovered_form hU hn θ
  calc Bridge U n θ = U n θ ⋆ refFam n (-θ) := rfl
    _ = (zexp (rateAlpha U n) (rateBeta U n) θ ⋆ Un n θ) ⋆ Un n (-θ) := by rw [h]; rfl
    _ = zexp (rateAlpha U n) (rateBeta U n) θ := by
        rw [mul_assoc_W, Un_mul_neg hn, mul_one_W]

/-- **PRINCIPAL THEOREM.**  The derived bridge of an arbitrary jointly regular family is a
**primitive bridge**, and the family it reconstructs is the original one.  No exactness is
used. -/
theorem bridge_isPrimitiveBridge {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) :
    IsPrimitiveBridge (Bridge U) ∧ ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ,
      recon (Bridge U) n θ = U n θ := by
  constructor
  · refine ⟨fun n hn θ => bridge_central hU hn θ, fun n hn => ?_, fun n hn θ φ => ?_, ?_⟩
    · rw [bridge_eq_zexp_general hU hn, zexp_zero]
    · rw [bridge_eq_zexp_general hU hn, bridge_eq_zexp_general hU hn,
        bridge_eq_zexp_general hU hn]
      exact (zexp_isCentralHom _ _).mul θ φ
    · have he : (fun p : Sph × ℝ => Bridge U (p.1 : Vec3) p.2)
          = fun p : Sph × ℝ => zc
            (Real.exp (rateAlpha U (p.1 : Vec3) * p.2) *
              Real.cos (rateBeta U (p.1 : Vec3) * p.2))
            (Real.exp (rateAlpha U (p.1 : Vec3) * p.2) *
              Real.sin (rateBeta U (p.1 : Vec3) * p.2)) := by
        funext p
        rw [bridge_eq_zexp_general hU p.1.2, zexp]
      rw [he]
      have hA : Continuous fun p : Sph × ℝ => rateAlpha U (p.1 : Vec3) :=
        (jointlyRegular_alpha_continuous hU).comp continuous_fst
      have hB : Continuous fun p : Sph × ℝ => rateBeta U (p.1 : Vec3) :=
        (jointlyRegular_beta_continuous hU).comp continuous_fst
      simp only [zc]
      exact (Continuous.smul (by fun_prop) continuous_const).add
        (Continuous.smul (by fun_prop) continuous_const)
  · intro n hn θ
    exact (bridge_factorization hU hn θ).symm

/-- **DERIVED.**  Conversely, the bridge of the family reconstructed from a primitive bridge
is that primitive bridge. -/
theorem bridge_recon {c : Vec3 → ℝ → W} {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    Bridge (recon c) n θ = c n θ :=
  (bridge_unique hn rfl).symm

/-! ## §15 — the local condition -/

/-- **NEUTRAL DEFINITION.**  A family is *locally exact* when it is exactly
transformation-valued on every inherited domain. -/
def IsLocallyExact (U : Vec3 → ℝ → W) : Prop :=
  ∀ v : Vec3, v ≠ 0 → IsTransformationValuedOn (Dom v) U

theorem transformationValuedOn_congr {D : Set Vec3} {U V : Vec3 → ℝ → W}
    (h : ∀ n ∈ D, ∀ θ : ℝ, U n θ = V n θ) (hU : IsTransformationValuedOn D U) :
    IsTransformationValuedOn D V := by
  intro n hn m hm θ φ hP
  rw [← h n hn θ, ← h m hm φ]
  exact hU n hn m hm θ φ hP

/-- **DERIVED.**  If the first rate of a primitive bridge vanishes on a set of unit
directions, the reconstructed family coincides there with the explicit presentation by the
directional rate. -/
theorem recon_eq_famOf {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) {D : Set Vec3}
    (hunit : UnitSet D) (hA : ∀ n ∈ D, primRateA c n = 0) :
    ∀ n ∈ D, ∀ θ : ℝ, recon c n θ = famOf (fun _ => 0) (primRateB c) n θ := by
  intro n hn θ
  rw [recon_apply, primitiveBridge_normal_form hc (hunit n hn) θ, hA n hn]
  rfl

/-- **PRINCIPAL THEOREM (§15).**  *Equivalence.*  The reconstruction of a primitive bridge
is locally exact **iff** its first rate vanishes and its directional rate is half-odd at
every unit direction. -/
theorem recon_locallyExact_iff {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) :
    IsLocallyExact (recon c) ↔
      ∀ n : Vec3, IsUnitAxis n → primRateA c n = 0 ∧ IsHalfOdd (primRateB c n) := by
  constructor
  · intro hloc n hn
    have hex := hloc n (isUnitAxis_ne_zero hn)
    obtain ⟨hα, k, hk⟩ :=
      pointwise_rates (primitiveBridge_jointlyRegular hc) hex (Dom_covers hn) hn
    exact ⟨hα, ⟨k, hk⟩⟩
  · intro hrates v hv
    have hunit : UnitSet (Dom v) := fun n hn => hn.1
    have hfam : IsTransformationValuedOn (Dom v) (famOf (fun _ => 0) (primRateB c)) :=
      famOfZ_exact_on hunit (fun n hn => (hrates n (hunit n hn)).2)
        (fun n hn hneg => absurd hneg (Dom_antipodal_free hn))
    exact transformationValuedOn_congr
      (fun n hn θ => (recon_eq_famOf hc hunit (fun m hm => (hrates m (hunit m hm)).1)
        n hn θ).symm) hfam

/-! ## §16 — the global condition -/

/-- **PRINCIPAL THEOREM (§16).**  *Equivalence.*  The reconstruction of a primitive bridge
is globally exact **iff** its first rate vanishes everywhere and its directional rate is
half-odd at every unit direction *and* odd under reversal.  The extra relation property,
compared with §15, is exactly reversal oddness. -/
theorem recon_globallyExact_iff {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c) :
    IsTransformationValued (recon c) ↔
      ((∀ n : Vec3, IsUnitAxis n → primRateA c n = 0) ∧ RateHalfOdd (primRateB c) ∧
        RateRev (primRateB c)) := by
  constructor
  · intro hex
    have hexOn : IsTransformationValuedOn allUnit (recon c) :=
      fun n hn m hm θ φ hP => hex n m θ φ hn hm hP
    obtain ⟨hα, hhalf, -, hodd⟩ :=
      admissible_necessary (primitiveBridge_jointlyRegular hc) allUnit_unitSet hexOn
    exact ⟨fun n hn => hα n hn, fun n hn => hhalf n hn,
      fun n hn => hodd n hn (isUnitAxis_neg hn)⟩
  · rintro ⟨hA, hhalf, hodd⟩
    have hfam : IsTransformationValuedOn allUnit (famOf (fun _ => 0) (primRateB c)) :=
      famOfZ_exact_on allUnit_unitSet (fun n hn => hhalf n hn)
        (fun n hn _ => hodd n hn)
    have hrec : IsTransformationValuedOn allUnit (recon c) :=
      transformationValuedOn_congr
        (fun n hn θ => (recon_eq_famOf hc allUnit_unitSet (fun m hm => hA m hm) n hn θ).symm)
        hfam
    intro n m θ φ hn hm hP
    exact hrec n hn m hm θ φ hP

/-! ## §17 — the three implications, separately -/

/-- **PRINCIPAL THEOREM (§17b).**  Primitive bridge **plus the local rate condition** gives
a locally exact family. -/
theorem primitiveBridge_locallyExact {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c)
    (hrates : ∀ n : Vec3, IsUnitAxis n → primRateA c n = 0 ∧ IsHalfOdd (primRateB c n)) :
    IsJointlyRegularFamily (recon c) ∧ IsLocallyExact (recon c) :=
  ⟨primitiveBridge_jointlyRegular hc, (recon_locallyExact_iff hc).2 hrates⟩

/-- **PRINCIPAL THEOREM (§17c).**  Primitive bridge **plus the global rate condition** gives
a globally exact family. -/
theorem primitiveBridge_globallyExact {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c)
    (hA : ∀ n : Vec3, IsUnitAxis n → primRateA c n = 0) (hhalf : RateHalfOdd (primRateB c))
    (hodd : RateRev (primRateB c)) :
    IsJointlyRegularFamily (recon c) ∧ IsTransformationValued (recon c) :=
  ⟨primitiveBridge_jointlyRegular hc, (recon_globallyExact_iff hc).2 ⟨hA, hhalf, hodd⟩⟩

/-! ## §19 — the rate predicate -/

/-- **NEUTRAL DEFINITION (§19).**  A *global rate*: continuous on the whole unit-direction
space, half-odd at every unit direction, and odd under reversal. -/
def IsGlobalRate (b : Vec3 → ℝ) : Prop := RateCont b ∧ RateHalfOdd b ∧ RateRev b

/-- **DERIVED.**  The primitive bridge attached to a rate function. -/
noncomputable def bridgeOfRate (b : Vec3 → ℝ) (n : Vec3) (θ : ℝ) : W := zexp 0 (b n) θ

theorem bridgeOfRate_isPrimitiveBridge {b : Vec3 → ℝ} (hb : RateCont b) :
    IsPrimitiveBridge (bridgeOfRate b) where
  central := fun n _ θ => zexp_mem_Z 0 (b n) θ
  unit := fun n _ => zexp_zero 0 (b n)
  mul := fun n _ θ φ => (zexp_isCentralHom 0 (b n)).mul θ φ
  cont := by
    have he : (fun p : Sph × ℝ => bridgeOfRate b (p.1 : Vec3) p.2)
        = fun p : Sph × ℝ => zc (Real.cos (b (p.1 : Vec3) * p.2))
            (Real.sin (b (p.1 : Vec3) * p.2)) := by
      funext p
      rw [bridgeOfRate, zexp_zero_val]
    rw [he]
    have hB : Continuous fun p : Sph × ℝ => b (p.1 : Vec3) := hb.comp continuous_fst
    have hmul : Continuous fun p : Sph × ℝ => b (p.1 : Vec3) * p.2 := hB.mul continuous_snd
    simp only [zc]
    exact ((Real.continuous_cos.comp hmul).smul continuous_const).add
      ((Real.continuous_sin.comp hmul).smul continuous_const)

theorem bridgeOfRate_rates {b : Vec3 → ℝ} (hb : RateCont b) {n : Vec3} (hn : IsUnitAxis n) :
    primRateA (bridgeOfRate b) n = 0 ∧ primRateB (bridgeOfRate b) n = b n := by
  obtain ⟨h1, h2⟩ := primitiveBridge_rates_unique (bridgeOfRate_isPrimitiveBridge hb) hn
    (α := 0) (β := b n) (fun _ => rfl)
  exact ⟨h1.symm, h2.symm⟩

/-! ## §20, §21 — the two equivalences -/

/-- **PRINCIPAL THEOREM (§20).**  *Equivalence, both directions proved.*  A primitive bridge
whose reconstruction is globally exact exists **iff** a global rate exists. -/
theorem primitiveBridge_iff_globalRate :
    (∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c)) ↔
      ∃ b : Vec3 → ℝ, IsGlobalRate b := by
  constructor
  · rintro ⟨c, hc, hex⟩
    obtain ⟨-, hhalf, hodd⟩ := (recon_globallyExact_iff hc).1 hex
    exact ⟨primRateB c, jointlyRegular_beta_continuous (primitiveBridge_jointlyRegular hc),
      hhalf, hodd⟩
  · rintro ⟨b, hcont, hhalf, hodd⟩
    refine ⟨bridgeOfRate b, bridgeOfRate_isPrimitiveBridge hcont,
      (recon_globallyExact_iff (bridgeOfRate_isPrimitiveBridge hcont)).2 ⟨?_, ?_, ?_⟩⟩
    · exact fun n hn => (bridgeOfRate_rates hcont hn).1
    · intro n hn
      rw [(bridgeOfRate_rates hcont hn).2]
      exact hhalf n hn
    · intro n hn
      rw [(bridgeOfRate_rates hcont (isUnitAxis_neg hn)).2, (bridgeOfRate_rates hcont hn).2]
      exact hodd n hn

/-- **PRINCIPAL THEOREM (§21).**  *Equivalence, both directions proved.*  A primitive bridge
whose reconstruction is globally exact exists **iff** a globally jointly regular exact
family exists.  The backward direction produces the primitive bridge from the family; no
exactness enters the definition of the bridge. -/
theorem primitiveBridge_iff_globalExactFamily :
    (∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c)) ↔
      ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U := by
  constructor
  · rintro ⟨c, hc, hex⟩
    exact ⟨recon c, primitiveBridge_jointlyRegular hc, hex⟩
  · rintro ⟨U, hU, hex⟩
    obtain ⟨hprim, hagree⟩ := bridge_isPrimitiveBridge hU
    refine ⟨Bridge U, hprim, ?_⟩
    exact transformationValued_congr hex (fun n hn θ => (hagree n hn θ).symm)

/-! ## §23 — the corrected endpoints -/

/-- **PRINCIPAL THEOREM (§23), the nonexistence, correctly named.**  Neither a global rate
nor a primitive bridge with globally exact reconstruction exists.  This is a *conjunction*
of two negations; the equivalence between the two existence statements is the separate
theorem `primitiveBridge_iff_globalRate`. -/
theorem no_global_rate_and_no_primitive_global_bridge :
    (¬ ∃ b : Vec3 → ℝ, IsGlobalRate b) ∧
      ¬ ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c) := by
  have hno : ¬ ∃ b : Vec3 → ℝ, IsGlobalRate b := by
    rintro ⟨b, hcont, hhalf, hodd⟩
    exact no_global_halfodd_odd_rate ⟨b, hcont, fun n hn => hhalf n hn, hodd⟩
  exact ⟨hno, fun h => hno (primitiveBridge_iff_globalRate.1 h)⟩

/-! ## §24 — primitive bridges exist -/

/-- **PRINCIPAL THEOREM (§24).**  Primitive bridges **exist**, and even ones whose
reconstruction is locally exact: the nonexistence statement above is therefore not an
artefact of inserting exactness into the definition.  The witness reconstructs the explicit
local model with label `0`. -/
theorem exists_primitiveBridge :
    ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsLocallyExact (recon c) ∧
      ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, recon c n θ = locFam 0 n θ := by
  have hc : IsPrimitiveBridge (cexp 0 (1 / 2)) := cexp_isPrimitiveBridge 0 (1 / 2)
  refine ⟨cexp 0 (1 / 2), hc, (recon_locallyExact_iff hc).2 (fun n hn => ?_), fun n _ θ => ?_⟩
  · rw [(cexp_rates 0 (1 / 2) hn).1, (cexp_rates 0 (1 / 2) hn).2]
    exact ⟨rfl, 0, by norm_num⟩
  · show zexp 0 (1 / 2) θ ⋆ Un n θ = zexp 0 ((0 : ℤ) + 1 / 2) θ ⋆ Un n θ
    norm_num

/-- **PRINCIPAL THEOREM (§24), the exact boundary.**  Existence of a primitive bridge is
*not* by itself the global obstruction: primitive bridges exist, locally exact ones exist,
and only the additional global rate condition fails. -/
theorem primitiveBridge_boundary :
    (∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c) ∧
      (∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsLocallyExact (recon c)) ∧
      ¬ ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c) := by
  obtain ⟨c, hc, hloc, -⟩ := exists_primitiveBridge
  exact ⟨⟨c, hc⟩, ⟨c, hc, hloc⟩, no_global_rate_and_no_primitive_global_bridge.2⟩

end NullSectorTask19
