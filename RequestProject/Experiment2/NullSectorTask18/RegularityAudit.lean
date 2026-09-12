import RequestProject.Experiment2.NullSectorTask18.DisconnectedDomains

/-!
# Task 18, Package I: arbitrary-domain continuous versus `C¹` admissibility

Task 17 proved that requiring continuously differentiable rate functions changes nothing
for the inherited domains `Dom v`, for antipodal-free domains, and for the antipodal
two-point domain.  Those three families of examples do **not** settle the arbitrary-domain
question, and the arbitrary-domain statement is not inferred from them here.

* §54.  `C¹` admissibility is defined with exactly the same domain quantifiers as
  continuous admissibility: a set of unit directions carrying a jointly `C¹` family which
  is exactly transformation-valued on it.
* §55.  The answer is **positive** for *every* set `D` of unit directions:
  `IsAdmissibleDomain D ↔ IsC1AdmissibleDomain D`.  The `C¹` rate is genuinely
  **constructed** from the continuous criterion, in four steps:
  1. the continuous rate is extended from the unit directions to the whole carrier and cut
     off, giving a continuous compactly supported function agreeing with it on the unit
     directions;
  2. that function is approximated within `1/4` by a smooth function;
  3. an explicit `C¹` *staircase* — a finite sum of translated smooth transitions — is
     built, which is exactly constant, with the value `k + 1/2`, on each interval
     `[k + 1/4, k + 3/4]` in the relevant range;
  4. the composition of the staircase with the smooth approximation is `C¹`, and *equals*
     the original rate at every direction of `D`, because the original rate is half-odd
     there.  Oddness on the antipodal pairs of `D` is inherited verbatim, since the two
     rates agree on `D`.

  No property of `D` is used at any step, so the result is genuinely arbitrary-domain.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## §54 — the notion -/

/-- **NEUTRAL DEFINITION (§54).**  `C¹` admissibility of an arbitrary set of directions,
with exactly the same quantifiers as `IsAdmissibleDomain`. -/
def IsC1AdmissibleDomain (D : Set Vec3) : Prop :=
  (∀ n ∈ D, IsUnitAxis n) ∧
    ∃ U : Vec3 → ℝ → W, IsC1JointlyRegularFamily U ∧ IsTransformationValuedOn D U

/-! ## The smooth staircase -/

/-- **NEUTRAL DEFINITION.**  A finite smooth staircase: the value `k + 1/2` is attained
exactly on `[k + 1/4, k + 3/4]` for every integer `k` with `|k| ≤ N`. -/
noncomputable def stair (N : ℕ) (x : ℝ) : ℝ :=
  -(N : ℝ) + 1 / 2 +
    ∑ j ∈ Finset.range (2 * N), Real.smoothTransition (2 * (x - (-(N : ℝ) + j + 3 / 4)))

theorem stair_contDiff (N : ℕ) : ContDiff ℝ 1 (stair N) := by
  unfold stair
  refine contDiff_const.add (ContDiff.sum ?_)
  intro j _
  have h : ContDiff ℝ 1 fun x : ℝ => 2 * (x - (-(N : ℝ) + j + 3 / 4)) :=
    (contDiff_id.sub contDiff_const).const_smul (2 : ℝ)
  exact (Real.smoothTransition.contDiff (n := 1)).comp h

/-- **DERIVED.**  The staircase is exactly flat, with the half-odd value, around every
half-odd number in its range. -/
theorem stair_eq (N : ℕ) (k : ℤ) (hk1 : -(N : ℤ) ≤ k) (hk2 : k ≤ (N : ℤ)) (x : ℝ)
    (hx : |x - ((k : ℝ) + 1 / 2)| ≤ 1 / 4) : stair N x = (k : ℝ) + 1 / 2 := by
  set i : ℕ := (k + N).toNat with hidef
  have hiZ : ((i : ℤ)) = k + N := Int.toNat_of_nonneg (by omega)
  have hik : (i : ℝ) = (k : ℝ) + (N : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hiZ
  have hile : i ≤ 2 * N := by omega
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have hsum : ∑ j ∈ Finset.range (2 * N),
      Real.smoothTransition (2 * (x - (-(N : ℝ) + j + 3 / 4)))
      = ∑ j ∈ Finset.range (2 * N), (if j < i then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hji : j < i
    · rw [if_pos hji]
      refine Real.smoothTransition.one_of_one_le ?_
      have hjr : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hji
      linarith
    · rw [if_neg hji]
      refine Real.smoothTransition.zero_of_nonpos ?_
      have hjr : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.le_of_not_lt hji
      linarith
  have hcount : ∑ j ∈ Finset.range (2 * N), (if j < i then (1 : ℝ) else 0) = (i : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
    congr 1
    have hfil : (Finset.range (2 * N)).filter (fun j => j < i) = Finset.range i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfil, Finset.card_range]
  rw [stair, hsum, hcount, hik]
  ring

/-! ## The unit directions are a compact closed set -/

theorem continuous_h3_self : Continuous fun w : Vec3 => h3 w w := by
  simp only [h3, dot3]
  fun_prop

theorem continuous_nrm : Continuous nrm := Real.continuous_sqrt.comp continuous_h3_self

theorem isClosed_unitSet : IsClosed {n : Vec3 | IsUnitAxis n} := by
  have he : {n : Vec3 | IsUnitAxis n} = (fun w : Vec3 => h3 w w) ⁻¹' {1} := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]; rfl
  rw [he]
  exact isClosed_singleton.preimage continuous_h3_self

theorem norm_le_of_h3_le {x : Vec3} {c : ℝ} (hc : 0 ≤ c) (h : h3 x x ≤ c ^ 2) : ‖x‖ ≤ c := by
  rw [h3_self_coord] at h
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have h1 : |x.1| ≤ c := by
    nlinarith [sq_nonneg x.2.1, sq_nonneg x.2.2, abs_nonneg x.1, sq_abs x.1]
  have h2 : |x.2.1| ≤ c := by
    nlinarith [sq_nonneg x.1, sq_nonneg x.2.2, abs_nonneg x.2.1, sq_abs x.2.1]
  have h3' : |x.2.2| ≤ c := by
    nlinarith [sq_nonneg x.1, sq_nonneg x.2.1, abs_nonneg x.2.2, sq_abs x.2.2]
  simp [h1, h2, h3']

theorem isCompact_unitSet : IsCompact {n : Vec3 | IsUnitAxis n} := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitSet ?_
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := 1)) ?_
  intro x hx
  have hxu : h3 x x = 1 := hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_h3_le zero_le_one (by rw [hxu]; norm_num)

/-- **DERIVED.**  A continuous rate function is bounded on the unit directions. -/
theorem rate_bounded {b : Vec3 → ℝ} (hb : Continuous fun s : Sph => b (s : Vec3)) :
    ∃ M : ℝ, ∀ n : Vec3, IsUnitAxis n → |b n| ≤ M := by
  have hcont : ContinuousOn b {n : Vec3 | IsUnitAxis n} := by
    rw [continuousOn_iff_continuous_restrict]
    exact hb
  obtain ⟨M, hM⟩ := isCompact_unitSet.exists_bound_of_continuousOn hcont
  exact ⟨M, fun n hn => by simpa [Real.norm_eq_abs] using hM n hn⟩

/-! ## The cut-off extension of a rate function -/

/-- **NEUTRAL DEFINITION.**  A cut-off profile: `1` at the unit radius, `0` below `1/2` and
above `2`. -/
noncomputable def cutoff (r : ℝ) : ℝ := max 0 (min (2 - r) (2 * r - 1))

theorem continuous_cutoff : Continuous cutoff := by
  unfold cutoff
  fun_prop

theorem cutoff_one : cutoff 1 = 1 := by
  rw [cutoff]
  norm_num

theorem cutoff_eq_zero {r : ℝ} (h : r ≤ 1 / 2 ∨ 2 ≤ r) : cutoff r = 0 := by
  rw [cutoff]
  rcases h with h | h
  · exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
  · exact max_eq_left (le_trans (min_le_left _ _) (by linarith))

/-- **DERIVED.**  Every continuous rate function on the unit directions extends to a
continuous, compactly supported function on the whole carrier. -/
theorem exists_compactSupport_extension {b : Vec3 → ℝ}
    (hb : Continuous fun s : Sph => b (s : Vec3)) :
    ∃ B : Vec3 → ℝ, Continuous B ∧ HasCompactSupport B ∧
      ∀ n : Vec3, IsUnitAxis n → B n = b n := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq (Y := ℝ) isClosed_unitSet
    (⟨fun s : Sph => b (s : Vec3), hb⟩ : C({n : Vec3 | IsUnitAxis n}, ℝ))
  have hGval : ∀ n : Vec3, IsUnitAxis n → G n = b n := by
    intro n hn
    have := congrArg (fun f : C({n : Vec3 | IsUnitAxis n}, ℝ) => f ⟨n, hn⟩) hG
    simpa using this
  refine ⟨fun x => cutoff (nrm x) * G x, (continuous_cutoff.comp continuous_nrm).mul G.continuous,
    ?_, ?_⟩
  · refine HasCompactSupport.intro (K := {x : Vec3 | nrm x ≤ 2}) ?_ ?_
    · refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_nrm continuous_const) ?_
      refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := 2)) ?_
      intro x hx
      have hx' : nrm x ≤ 2 := hx
      have h0 : 0 ≤ nrm x := Real.sqrt_nonneg _
      have hsq : h3 x x ≤ 2 ^ 2 := by
        rw [← nrm_sq x]; nlinarith
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_h3_le (by norm_num) hsq
    · intro x hx
      have hx' : ¬ nrm x ≤ 2 := hx
      rw [cutoff_eq_zero (Or.inr (by linarith [not_le.1 hx'])), zero_mul]
  · intro n hn
    have hnrm : nrm n = 1 := by
      have hnn : h3 n n = 1 := hn
      show Real.sqrt (h3 n n) = 1
      rw [hnn, Real.sqrt_one]
    show cutoff (nrm n) * G n = b n
    rw [hnrm, cutoff_one, one_mul, hGval n hn]

/-! ## §55 — the equivalence -/

/-- **PRINCIPAL THEOREM (§55), the construction.**  Every rate function which is continuous
on the unit directions and half-odd on an arbitrary set `D` of unit directions is matched on
`D` by a **continuously differentiable** function of the direction. -/
theorem exists_c1_rate {b : Vec3 → ℝ} (hb : Continuous fun s : Sph => b (s : Vec3))
    {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hhalf : ∀ n ∈ D, ∃ k : ℤ, b n = (k : ℝ) + 1 / 2) :
    ∃ c : Vec3 → ℝ, ContDiff ℝ 1 c ∧ ∀ n ∈ D, c n = b n := by
  obtain ⟨B, hBcont, hBsupp, hBval⟩ := exists_compactSupport_extension hb
  obtain ⟨g, hgsmooth, hgapp⟩ :=
    (hBsupp.uniformContinuous_of_continuous hBcont).exists_contDiff_dist_le
      (ε := 1 / 4) (by norm_num)
  obtain ⟨M, hM⟩ := rate_bounded hb
  obtain ⟨N, hN⟩ := exists_nat_ge (M + 1)
  refine ⟨stair N ∘ g, (stair_contDiff N).comp (hgsmooth.of_le (by norm_num)), ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := hhalf n hn
  have hbn : |b n| ≤ M := hM n (hunit n hn)
  have hkM : |((k : ℝ) + 1 / 2)| ≤ M := by rw [← hk]; exact hbn
  have hkabs : |(k : ℝ)| ≤ (N : ℝ) := by
    rcases abs_le.1 hkM with ⟨h1, h2⟩
    rw [abs_le]
    constructor <;> linarith
  have hk1 : -(N : ℤ) ≤ k := by
    have : -(N : ℝ) ≤ (k : ℝ) := (abs_le.1 hkabs).1
    exact_mod_cast this
  have hk2 : k ≤ (N : ℤ) := by
    have : (k : ℝ) ≤ (N : ℝ) := (abs_le.1 hkabs).2
    exact_mod_cast this
  have hdist : |g n - ((k : ℝ) + 1 / 2)| ≤ 1 / 4 := by
    have h1 : dist (g n) (B n) < 1 / 4 := hgapp n
    rw [Real.dist_eq, hBval n (hunit n hn), hk] at h1
    linarith [le_of_lt h1]
  show stair N (g n) = b n
  rw [stair_eq N k hk1 hk2 (g n) hdist, hk]

/-- **PRINCIPAL THEOREM (§55).**  For **every** set of unit directions, continuous
admissibility and `C¹` admissibility coincide.  The forward direction constructs the `C¹`
rate; the backward direction is immediate. -/
theorem admissible_iff_c1Admissible {D : Set Vec3} :
    IsAdmissibleDomain D ↔ IsC1AdmissibleDomain D := by
  constructor
  · rintro ⟨hunit, U, hU, hexact⟩
    obtain ⟨b, hcont, hhalf, hodd⟩ := (admissible_iff_exists_rate_function hunit).1
      ⟨hunit, U, hU, hexact⟩
    obtain ⟨c, hc1, hcval⟩ := exists_c1_rate hcont hunit hhalf
    have hchalf : ∀ n ∈ D, ∃ k : ℤ, c n = (k : ℝ) + 1 / 2 := by
      intro n hn
      obtain ⟨k, hk⟩ := hhalf n hn
      exact ⟨k, by rw [hcval n hn, hk]⟩
    have hcodd : ∀ n ∈ D, -n ∈ D → c (-n) = -c n := by
      intro n hn hneg
      rw [hcval n hn, hcval (-n) hneg]
      exact hodd n hn hneg
    have hccont : Continuous fun s : Sph => c (s : Vec3) :=
      (hc1.continuous).comp continuous_subtype_val
    refine ⟨hunit, famOf (fun _ => 0) c, ⟨jointlyRegular_famOf continuous_const hccont,
      fun _ => 0, c, contDiff_const, hc1, fun _ _ _ => rfl⟩, ?_⟩
    exact famOfZ_exact_on hunit hchalf hcodd
  · rintro ⟨hunit, U, hU, hexact⟩
    exact ⟨hunit, U, hU.toJointlyRegular, hexact⟩

/-- **DERIVED (§55).**  In particular the `C¹` requirement restricts neither the admissible
domains nor, by the Task-17 classification, the labels or the overlap factors. -/
theorem c1_admissibility_adds_nothing (D : Set Vec3) :
    (IsAdmissibleDomain D → IsC1AdmissibleDomain D) ∧
      (IsC1AdmissibleDomain D → IsAdmissibleDomain D) :=
  ⟨admissible_iff_c1Admissible.1, admissible_iff_c1Admissible.2⟩

end NullSectorTask18
