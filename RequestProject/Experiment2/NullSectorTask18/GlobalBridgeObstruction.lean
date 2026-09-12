import RequestProject.Experiment2.NullSectorTask18.BridgeReconstruction

/-!
# Task 18, Package F: where the global exact no-go reappears

Package E showed that bridge-normalization of local data never fails.  The question is
therefore where the inherited global obstruction survives.  The answer proved here is:
**exactly** in the nonexistence of *one global bridge*.

* §41.  A **global bridge** is a central-valued function of direction and parameter whose
  product with the global sign-relaxed reference is a jointly regular family that is
  exactly transformation-valued at *all* unit directions.
* §42, §43.  The equivalence

  ```
  (∃ globally exact jointly regular representative) ↔ (∃ global bridge)
  ```

  is **valid**, and both directions are proved separately: the forward direction takes the
  derived bridge of the representative (Package D), the backward direction takes the
  product family.  The inherited global no-go is then *exactly* the nonexistence of a
  global bridge.
* §44.  Where continuity, half-oddness and reversal enter is determined formally, rather
  than asserted: a global bridge is `zexp 0 (b n) θ` for a rate `b` which is forced to be
  (i) continuous on the unit directions — by joint regularity, (ii) half-odd at *every*
  unit direction — by exactness at each single direction, (iii) odd under reversal — by
  exactness across the antipodal coincidence.  Each **pair** of the three conditions is
  realizable by an explicit rate; only the three together are impossible.  Reversal
  oddness alone is therefore not "the" obstruction.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## Transfer of joint regularity along equality at unit directions -/

/-- **DERIVED.**  Joint regularity depends only on the values at unit directions. -/
theorem jointlyRegular_congr {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (h : ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = V n θ) : IsJointlyRegularFamily V := by
  refine ⟨fun n hn => ?_, ?_⟩
  · have hlift := hU.lift n hn
    rwa [show U n = V n from funext (h n hn)] at hlift
  · have he : (fun p : Sph × ℝ => V (p.1 : Vec3) p.2)
        = fun p : Sph × ℝ => U (p.1 : Vec3) p.2 := by
      funext p
      exact (h (p.1 : Vec3) p.1.2 p.2).symm
    rw [he]
    exact hU.joint

/-- **DERIVED.**  Exact transformation-valuedness likewise depends only on the values at
unit directions. -/
theorem transformationValued_congr {U V : Vec3 → ℝ → W} (hU : IsTransformationValued U)
    (h : ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = V n θ) : IsTransformationValued V := by
  intro n m θ φ hn hm hP
  rw [← h n hn θ, ← h m hm φ]
  exact hU n m θ φ hn hm hP

/-! ## §41 — the notion of a global bridge -/

/-- **NEUTRAL DEFINITION (§41).**  A *global bridge* to the unique global sign-relaxed
reference: a central factor at every unit direction whose product with the reference is a
jointly regular family that is exactly transformation-valued everywhere.  The factor is
carried explicitly; nothing is quotiented. -/
def IsGlobalBridge (c : Vec3 → ℝ → W) : Prop :=
  (∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, c n θ ∈ Z) ∧
    IsJointlyRegularFamily (fun n θ => c n θ ⋆ refFam n θ) ∧
    IsTransformationValued (fun n θ => c n θ ⋆ refFam n θ)

/-! ## §42, §43 — the equivalence, both directions -/

/-- **PRINCIPAL THEOREM (§42), forward direction.**  A globally exact jointly regular
representative *has* a global bridge, namely its own derived bridge. -/
theorem globalBridge_of_globalExact {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hex : IsTransformationValued U) : IsGlobalBridge (Bridge U) := by
  have hagree : ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = Bridge U n θ ⋆ refFam n θ :=
    fun n hn θ => bridge_factorization hU hn θ
  exact ⟨fun n hn θ => bridge_central hU hn θ, jointlyRegular_congr hU hagree,
    transformationValued_congr hex hagree⟩

/-- **PRINCIPAL THEOREM (§42), backward direction.**  A global bridge *produces* a globally
exact jointly regular representative. -/
theorem globalExact_of_globalBridge {c : Vec3 → ℝ → W} (hc : IsGlobalBridge c) :
    IsJointlyRegularFamily (fun n θ => c n θ ⋆ refFam n θ) ∧
      IsTransformationValued (fun n θ => c n θ ⋆ refFam n θ) :=
  ⟨hc.2.1, hc.2.2⟩

/-- **PRINCIPAL THEOREM (§42).**  The equivalence is valid. -/
theorem globalExact_iff_globalBridge :
    (∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U) ↔
      ∃ c : Vec3 → ℝ → W, IsGlobalBridge c := by
  constructor
  · rintro ⟨U, hU, hex⟩
    exact ⟨Bridge U, globalBridge_of_globalExact hU hex⟩
  · rintro ⟨c, hc⟩
    exact ⟨_, hc.2.1, hc.2.2⟩

/-- **PRINCIPAL THEOREM (§43).**  Consequently the inherited global exact no-go *is* the
nonexistence of one global bridge. -/
theorem no_global_bridge : ¬ ∃ c : Vec3 → ℝ → W, IsGlobalBridge c := by
  intro h
  exact no_global_jointly_regular_transformationValued (globalExact_iff_globalBridge.2 h)

/-! ## §44 — where continuity, half-oddness and reversal enter -/

/-- **PRINCIPAL THEOREM (§44).**  A global bridge is the central one-parameter element of a
rate function, and that rate is forced to satisfy all three conditions at once: continuity
on the unit directions, half-oddness at every unit direction, and oddness under
reversal. -/
theorem globalBridge_rate_conditions {c : Vec3 → ℝ → W} (hc : IsGlobalBridge c) :
    ∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
      (∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n)) ∧
      (∀ n : Vec3, IsUnitAxis n → b (-n) = -b n) ∧
      (∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, c n θ = zexp 0 (b n) θ) := by
  obtain ⟨-, hreg, hex⟩ := hc
  set U : Vec3 → ℝ → W := fun n θ => c n θ ⋆ refFam n θ with hUdef
  have hexOn : IsTransformationValuedOn {n : Vec3 | IsUnitAxis n} U := by
    intro n hn m hm θ φ hP
    exact hex n m θ φ hn hm hP
  have hunit : ∀ n ∈ {n : Vec3 | IsUnitAxis n}, IsUnitAxis n := fun _ h => h
  obtain ⟨hα, hhalf, hcont, hodd⟩ := admissible_necessary hreg hunit hexOn
  refine ⟨rateBeta U, hcont, fun n hn => hhalf n hn, fun n hn => hodd n hn (isUnitAxis_neg hn),
    fun n hn θ => ?_⟩
  have hbridge : c n θ = Bridge U n θ := bridge_unique hn rfl
  rw [hbridge, bridge_eq_zexp hreg hn (hα n hn) θ]

/-- **NEUTRAL DEFINITION.**  The explicit discontinuous rate: the half-odd value `1/2` on
the lexicographic half-space and `-1/2` on its reverse. -/
noncomputable def signRate (n : Vec3) : ℝ := open Classical in if n ∈ lexA then 1 / 2 else -(1 / 2)

theorem signRate_halfOdd (n : Vec3) : IsHalfOdd (signRate n) := by
  classical
  by_cases h : n ∈ lexA
  · exact ⟨0, by rw [signRate, if_pos h]; norm_num⟩
  · exact ⟨-1, by rw [signRate, if_neg h]; norm_num⟩

theorem signRate_odd {n : Vec3} (hn : IsUnitAxis n) : signRate (-n) = -signRate n := by
  classical
  rcases lexA_exactly_one hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [signRate, signRate, if_pos h1, if_neg h2]
  · rw [signRate, signRate, if_neg h1, if_pos h2]
    norm_num

/-- **PRINCIPAL THEOREM (§44).**  Each **pair** of the three conditions is realizable by an
explicit rate; only all three together are impossible.  Reversal oddness alone is therefore
not the obstruction, and neither is half-oddness alone, nor continuity alone. -/
theorem three_conditions_pairwise_realizable :
    -- continuous and reversal-odd, but not half-odd
    (∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
      (∀ n : Vec3, IsUnitAxis n → b (-n) = -b n) ∧
      ¬ (∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n))) ∧
    -- continuous and half-odd, but not reversal-odd
    (∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
      (∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n)) ∧
      ¬ (∀ n : Vec3, IsUnitAxis n → b (-n) = -b n)) ∧
    -- half-odd and reversal-odd, but not continuous
    (∃ b : Vec3 → ℝ, (∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n)) ∧
      (∀ n : Vec3, IsUnitAxis n → b (-n) = -b n) ∧
      ¬ (Continuous fun s : Sph => b (s : Vec3))) := by
  refine ⟨⟨fun _ => 0, continuous_const, fun _ _ => by norm_num, ?_⟩,
    ⟨fun _ => 1 / 2, continuous_const, fun _ _ => ⟨0, by norm_num⟩, ?_⟩,
    ⟨signRate, fun n _ => signRate_halfOdd n, fun n hn => signRate_odd hn, ?_⟩⟩
  · intro hcon
    obtain ⟨k, hk⟩ := hcon e1 e1_isUnitAxis
    have : (2 * k : ℤ) = -1 := by
      have : (2 * (k : ℝ)) = -1 := by
        have h0 : (0 : ℝ) = (k : ℝ) + 1 / 2 := hk
        linarith
      exact_mod_cast this
    omega
  · intro hcon
    have := hcon e1 e1_isUnitAxis
    norm_num at this
  · intro hcont
    exact no_global_halfodd_odd_rate
      ⟨signRate, hcont, fun n hn => signRate_halfOdd n, fun n hn => signRate_odd hn⟩

/-- **PRINCIPAL THEOREM (§44), the exact location of the obstruction.**  No rate function
satisfies the three conditions simultaneously, and this — not any defect of the overlap or
of the conversion data — is precisely what prevents a global bridge. -/
theorem no_global_bridge_iff_no_rate :
    (¬ ∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
        (∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n)) ∧
        (∀ n : Vec3, IsUnitAxis n → b (-n) = -b n)) ∧
      (¬ ∃ c : Vec3 → ℝ → W, IsGlobalBridge c) := by
  refine ⟨?_, no_global_bridge⟩
  rintro ⟨b, hcont, hhalf, hodd⟩
  exact no_global_halfodd_odd_rate ⟨b, hcont, fun n hn => hhalf n hn, hodd⟩

end NullSectorTask18
